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
      var s7 := Push2(s6, 0x00f2);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s554(s8, gas - 1)
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
      var s6 := Push4(s5, 0x7d1db4a5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0087);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s9, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0057);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02a5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s142(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc9567bf9);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02c4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02d8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s5, gas - 1)
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
      var s2 := Push4(s1, 0xfc76729c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x031c);
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
    * Segment Id for this node is: 82
    * Starting at 0x31c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
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
      var s5 := Push2(s4, 0x0327);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s6, gas - 1)
      else
        ExecuteFromCFGNode_s9(s6, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 83
    * Starting at 0x324
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x324 as nat
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
    * Segment Id for this node is: 84
    * Starting at 0x327
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x327 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0213);
      var s4 := Push2(s3, 0x08a9);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 140
    * Starting at 0x8a9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x213;
      var s12 := Push2(s11, 0x08d2);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s13, gas - 1)
      else
        ExecuteFromCFGNode_s12(s13, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 141
    * Starting at 0x8bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x213;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3f6;
      assert s11.Peek(2) == 0x213;
      var s12 := Push2(s11, 0x10c4);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s13, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 240
    * Starting at 0x10c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x3f6

    requires s0.stack[2] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3f6;
      assert s1.Peek(2) == 0x213;
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
      assert s11.Peek(3) == 0x3f6;
      assert s11.Peek(4) == 0x213;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s18, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
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

  /** Node 15
    * Segment Id for this node is: 142
    * Starting at 0x8d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(4) == 0x213;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := And(s13);
      var s15 := Swap2(s14);
      var s16 := SelfBalance(s15);
      var s17 := Dup1(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x08fc);
      var s20 := Mul(s19);
      var s21 := Swap3(s20);
      assert s21.Peek(5) == 0x213;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Dup2(s23);
      var s25 := Dup2(s24);
      var s26 := Dup2(s25);
      var s27 := Dup6(s26);
      var s28 := Dup9(s27);
      var s29 := Dup9(s28);
      var s30 := Call(s29);
      var s31 := Swap4(s30);
      assert s31.Peek(5) == 0x213;
      var s32 := Pop(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := IsZero(s35);
      var s37 := Dup1(s36);
      var s38 := IsZero(s37);
      var s39 := Push2(s38, 0x0909);
      var s40 := JumpI(s39);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s39.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s40, gas - 1)
      else
        ExecuteFromCFGNode_s16(s40, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 143
    * Starting at 0x902
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x902 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(2) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 17
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s3, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 55
    * Starting at 0x213
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
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

  /** Node 19
    * Segment Id for this node is: 78
    * Starting at 0x2d8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
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
      var s5 := Push2(s4, 0x02e3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s6, gas - 1)
      else
        ExecuteFromCFGNode_s20(s6, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 79
    * Starting at 0x2e0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e0 as nat
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

  /** Node 21
    * Segment Id for this node is: 80
    * Starting at 0x2e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0183);
      var s4 := Push2(s3, 0x02f2);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0f74);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s8, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 206
    * Starting at 0xf74
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf74 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2f2

    requires s0.stack[3] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2f2;
      assert s1.Peek(3) == 0x183;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f85);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s11, gas - 1)
      else
        ExecuteFromCFGNode_s23(s11, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 207
    * Starting at 0xf82
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2f2

    requires s0.stack[5] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x2f2;
      assert s1.Peek(6) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 208
    * Starting at 0xf85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2f2

    requires s0.stack[5] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2f2;
      assert s1.Peek(5) == 0x183;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0f90);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s7, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf90

    requires s0.stack[7] == 0x2f2

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf90;
      assert s1.Peek(7) == 0x2f2;
      assert s1.Peek(8) == 0x183;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xf90;
      assert s11.Peek(9) == 0x2f2;
      assert s11.Peek(10) == 0x183;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s12, gas - 1)
      else
        ExecuteFromCFGNode_s26(s12, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf90

    requires s0.stack[7] == 0x2f2

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xf90;
      assert s1.Peek(8) == 0x2f2;
      assert s1.Peek(9) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 27
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf90

    requires s0.stack[7] == 0x2f2

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf90;
      assert s1.Peek(7) == 0x2f2;
      assert s1.Peek(8) == 0x183;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s3, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 209
    * Starting at 0xf90
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf90 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2f2

    requires s0.stack[6] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2f2;
      assert s1.Peek(6) == 0x183;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0fa0);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0edd);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s11, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfa0

    requires s0.stack[7] == 0x2f2

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa0;
      assert s1.Peek(7) == 0x2f2;
      assert s1.Peek(8) == 0x183;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xfa0;
      assert s11.Peek(9) == 0x2f2;
      assert s11.Peek(10) == 0x183;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s12, gas - 1)
      else
        ExecuteFromCFGNode_s30(s12, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfa0

    requires s0.stack[7] == 0x2f2

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xfa0;
      assert s1.Peek(8) == 0x2f2;
      assert s1.Peek(9) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 31
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xfa0

    requires s0.stack[7] == 0x2f2

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xfa0;
      assert s1.Peek(7) == 0x2f2;
      assert s1.Peek(8) == 0x183;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s3, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 210
    * Starting at 0xfa0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2f2

    requires s0.stack[6] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2f2;
      assert s1.Peek(6) == 0x183;
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
      ExecuteFromCFGNode_s33(s11, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 81
    * Starting at 0x2f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x183;
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
      assert s11.Peek(4) == 0x183;
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
      assert s21.Peek(7) == 0x183;
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
      assert s31.Peek(4) == 0x183;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s36, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 40
    * Starting at 0x183
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x183 as nat
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
      var s9 := Push2(s8, 0x0137);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s10, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 31
    * Starting at 0x137
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137 as nat
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

  /** Node 36
    * Segment Id for this node is: 75
    * Starting at 0x2c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c4 as nat
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
      var s5 := Push2(s4, 0x02cf);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s6, gas - 1)
      else
        ExecuteFromCFGNode_s37(s6, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 76
    * Starting at 0x2cc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
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

  /** Node 38
    * Segment Id for this node is: 77
    * Starting at 0x2cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0213);
      var s4 := Push2(s3, 0x0504);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 110
    * Starting at 0x504
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x504 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x213;
      var s12 := Push2(s11, 0x052d);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s13, gas - 1)
      else
        ExecuteFromCFGNode_s40(s13, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 111
    * Starting at 0x516
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x516 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x213;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3f6;
      assert s11.Peek(2) == 0x213;
      var s12 := Push2(s11, 0x10c4);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s13, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 112
    * Starting at 0x52d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Swap1(s6);
      var s8 := Div(s7);
      var s9 := Push1(s8, 0xff);
      var s10 := And(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(1) == 0x213;
      var s12 := Push2(s11, 0x0587);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s13, gas - 1)
      else
        ExecuteFromCFGNode_s42(s13, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 113
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x213;
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
      assert s11.Peek(3) == 0x213;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x17);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x74726164696e6720697320616c7265616479206f70656e000000000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x213;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s26, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 114
    * Starting at 0x587
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x587 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push1(s1, 0x05);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Not(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x213;
      var s12 := Push20(s11, 0x7a250d5630b4cf539739df2c5dacb4c659f2488d);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Or(s14);
      var s16 := Swap1(s15);
      var s17 := Swap2(s16);
      var s18 := SStore(s17);
      var s19 := Push2(s18, 0x05d0);
      var s20 := Swap1(s19);
      var s21 := Address(s20);
      assert s21.Peek(2) == 0x5d0;
      assert s21.Peek(3) == 0x213;
      var s22 := Swap1(s21);
      var s23 := Push2(s22, 0x05c2);
      var s24 := Push1(s23, 0x09);
      var s25 := Push1(s24, 0x0a);
      var s26 := Push2(s25, 0x109f);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s27, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 237
    * Starting at 0x109f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x5c2

    requires s0.stack[5] == 0x5d0

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5c2;
      assert s1.Peek(5) == 0x5d0;
      assert s1.Peek(6) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x1001);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s9, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 220
    * Starting at 0x1001
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1001 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xe2d

    requires s0.stack[6] == 0x5c2

    requires s0.stack[9] == 0x5d0

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x5c2;
      assert s1.Peek(9) == 0x5d0;
      assert s1.Peek(10) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x100f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s5, gas - 1)
      else
        ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 221
    * Starting at 0x1008
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1008 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x5c2;
      assert s1.Peek(9) == 0x5d0;
      assert s1.Peek(10) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s4, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(11) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s6, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x5c2

    requires s0.stack[7] == 0x5d0

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5c2;
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(8) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s7, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 115
    * Starting at 0x5c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(4) == 0x213;
      var s2 := Push2(s1, 0x03be);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x05f5e100);
      var s5 := Push2(s4, 0x10ad);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s6, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 238
    * Starting at 0x10ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x3be

    requires s0.stack[5] == 0x5d0

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3be;
      assert s1.Peek(5) == 0x5d0;
      assert s1.Peek(6) == 0x213;
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
      assert s11.Peek(5) == 0x3be;
      assert s11.Peek(8) == 0x5d0;
      assert s11.Peek(9) == 0x213;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0340);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s14, gas - 1)
      else
        ExecuteFromCFGNode_s51(s14, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 239
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x3be

    requires s0.stack[6] == 0x5d0

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x3be;
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(8) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0x3be

    requires s0.stack[7] == 0x5d0

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x3be;
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(8) == 0x213;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0x3be;
      assert s11.Peek(9) == 0x5d0;
      assert s11.Peek(10) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 53
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x3be

    requires s0.stack[6] == 0x5d0

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3be;
      assert s1.Peek(6) == 0x5d0;
      assert s1.Peek(7) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 94
    * Starting at 0x3be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(4) == 0x213;
      var s2 := Push2(s1, 0x090c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s3, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 145
    * Starting at 0x90c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(4) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x096e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s10, gas - 1)
      else
        ExecuteFromCFGNode_s56(s10, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 146
    * Starting at 0x91b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(5) == 0x213;
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
      assert s11.Peek(6) == 0x5d0;
      assert s11.Peek(7) == 0x213;
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
      assert s21.Peek(6) == 0x5d0;
      assert s21.Peek(7) == 0x213;
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
      assert s31.Peek(4) == 0x5d0;
      assert s31.Peek(5) == 0x213;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s33, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x5d0

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(5) == 0x213;
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

  /** Node 58
    * Segment Id for this node is: 147
    * Starting at 0x96e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(4) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x09cf);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s10, gas - 1)
      else
        ExecuteFromCFGNode_s59(s10, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 148
    * Starting at 0x97d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x5d0;
      assert s1.Peek(5) == 0x213;
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
      assert s11.Peek(6) == 0x5d0;
      assert s11.Peek(7) == 0x213;
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
      assert s21.Peek(6) == 0x5d0;
      assert s21.Peek(7) == 0x213;
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
      assert s31.Peek(4) == 0x5d0;
      assert s31.Peek(5) == 0x213;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s33, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 149
    * Starting at 0x9cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x5d0

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d0;
      assert s1.Peek(4) == 0x213;
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
      assert s11.Peek(7) == 0x5d0;
      assert s11.Peek(8) == 0x213;
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
      assert s21.Peek(10) == 0x5d0;
      assert s21.Peek(11) == 0x213;
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
      assert s31.Peek(8) == 0x5d0;
      assert s31.Peek(9) == 0x213;
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
      ExecuteFromCFGNode_s61(s41, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 150
    * Starting at 0x9fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x5d0

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x5d0;
      assert s1.Peek(10) == 0x213;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s5, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 151
    * Starting at 0xa23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x5d0

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x5d0;
      assert s1.Peek(8) == 0x213;
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
      assert s11.Peek(0) == 0x5d0;
      assert s11.Peek(1) == 0x213;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s12, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 116
    * Starting at 0x5d0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push1(s1, 0x05);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(2) == 0x213;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := And(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(2) == 0x213;
      var s22 := And(s21);
      var s23 := Push4(s22, 0xc45a0155);
      var s24 := Push1(s23, 0x40);
      var s25 := MLoad(s24);
      var s26 := Dup2(s25);
      var s27 := Push4(s26, 0xffffffff);
      var s28 := And(s27);
      var s29 := Push1(s28, 0xe0);
      var s30 := Shl(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(5) == 0x213;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x04);
      var s34 := Add(s33);
      var s35 := Push1(s34, 0x20);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Dup1(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s64(s41, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 117
    * Starting at 0x60f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup7(s0);
      assert s1.Peek(8) == 0x213;
      var s2 := Gas(s1);
      var s3 := StaticCall(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0620);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s8, gas - 1)
      else
        ExecuteFromCFGNode_s65(s8, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 118
    * Starting at 0x619
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x619 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 66
    * Segment Id for this node is: 119
    * Starting at 0x620
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x213;
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
      assert s11.Peek(4) == 0x213;
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
      assert s21.Peek(3) == 0x213;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0644);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x10f9);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s28, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 241
    * Starting at 0x10f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x644

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x644;
      assert s1.Peek(3) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1109);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s10, gas - 1)
      else
        ExecuteFromCFGNode_s68(s10, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 242
    * Starting at 0x1106
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x644

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x644;
      assert s1.Peek(5) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 69
    * Segment Id for this node is: 243
    * Starting at 0x1109
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x644

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x644;
      assert s1.Peek(4) == 0x213;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0e2d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s7, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x644

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x644;
      assert s1.Peek(7) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xe2d;
      assert s11.Peek(8) == 0x644;
      assert s11.Peek(9) == 0x213;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s12, gas - 1)
      else
        ExecuteFromCFGNode_s71(s12, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x644

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(7) == 0x644;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 72
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x644

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x644;
      assert s1.Peek(7) == 0x213;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x644

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x644;
      assert s1.Peek(5) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s7, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 120
    * Starting at 0x644
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push4(s7, 0xc9c65396);
      var s9 := Address(s8);
      var s10 := Push1(s9, 0x05);
      var s11 := Push0(s10);
      assert s11.Peek(5) == 0x213;
      var s12 := Swap1(s11);
      var s13 := SLoad(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x0100);
      var s16 := Exp(s15);
      var s17 := Swap1(s16);
      var s18 := Div(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0xa0);
      assert s21.Peek(7) == 0x213;
      var s22 := Shl(s21);
      var s23 := Sub(s22);
      var s24 := And(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0x01);
      var s27 := Push1(s26, 0xa0);
      var s28 := Shl(s27);
      var s29 := Sub(s28);
      var s30 := And(s29);
      var s31 := Push4(s30, 0xad5c4648);
      assert s31.Peek(5) == 0x213;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Dup2(s33);
      var s35 := Push4(s34, 0xffffffff);
      var s36 := And(s35);
      var s37 := Push1(s36, 0xe0);
      var s38 := Shl(s37);
      var s39 := Dup2(s38);
      var s40 := MStore(s39);
      var s41 := Push1(s40, 0x04);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s75(s41, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 121
    * Starting at 0x688
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x688 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(6) == 0x213;
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
      assert s11.Peek(7) == 0x213;
      var s12 := IsZero(s11);
      var s13 := Dup1(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x06a3);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s16, gas - 1)
      else
        ExecuteFromCFGNode_s76(s16, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 122
    * Starting at 0x69c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(8) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 77
    * Segment Id for this node is: 123
    * Starting at 0x6a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x213;
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
      assert s11.Peek(7) == 0x213;
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
      assert s21.Peek(6) == 0x213;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x06c7);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x10f9);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s28, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 241
    * Starting at 0x10f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x6c7

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x6c7;
      assert s1.Peek(6) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1109);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s10, gas - 1)
      else
        ExecuteFromCFGNode_s79(s10, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 242
    * Starting at 0x1106
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x6c7

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x6c7;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 80
    * Segment Id for this node is: 243
    * Starting at 0x1109
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x6c7

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x6c7;
      assert s1.Peek(7) == 0x213;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0e2d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s7, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x6c7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x6c7;
      assert s1.Peek(10) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xe2d;
      assert s11.Peek(8) == 0x6c7;
      assert s11.Peek(12) == 0x213;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s12, gas - 1)
      else
        ExecuteFromCFGNode_s82(s12, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x6c7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(7) == 0x6c7;
      assert s1.Peek(11) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 83
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x6c7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x6c7;
      assert s1.Peek(10) == 0x213;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s3, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x6c7

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x6c7;
      assert s1.Peek(8) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s7, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 124
    * Starting at 0x6c7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x213;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xe0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Not(s8);
      var s10 := Push1(s9, 0xe0);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x213;
      var s12 := Swap1(s11);
      var s13 := Shl(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x213;
      var s22 := Swap3(s21);
      var s23 := Dup4(s22);
      var s24 := And(s23);
      var s25 := Push1(s24, 0x04);
      var s26 := Dup3(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := Swap2(s28);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x24);
      assert s31.Peek(5) == 0x213;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x44);
      var s36 := Add(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Dup1(s39);
      var s41 := Dup4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s86(s41, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 125
    * Starting at 0x6fd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(6) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push0(s2);
      var s4 := Dup8(s3);
      var s5 := Gas(s4);
      var s6 := Call(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0711);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s11, gas - 1)
      else
        ExecuteFromCFGNode_s87(s11, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 126
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 88
    * Segment Id for this node is: 127
    * Starting at 0x711
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x711 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x213;
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
      assert s11.Peek(4) == 0x213;
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
      assert s21.Peek(3) == 0x213;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0735);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x10f9);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s89(s28, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 241
    * Starting at 0x10f9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x735

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x735;
      assert s1.Peek(3) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1109);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s10, gas - 1)
      else
        ExecuteFromCFGNode_s90(s10, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 242
    * Starting at 0x1106
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x735

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x735;
      assert s1.Peek(5) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 91
    * Segment Id for this node is: 243
    * Starting at 0x1109
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1109 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x735

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x735;
      assert s1.Peek(4) == 0x213;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0e2d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s7, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x735

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x735;
      assert s1.Peek(7) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xe2d;
      assert s11.Peek(8) == 0x735;
      assert s11.Peek(9) == 0x213;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s12, gas - 1)
      else
        ExecuteFromCFGNode_s93(s12, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x735

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(7) == 0x735;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 94
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x735

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x735;
      assert s1.Peek(7) == 0x213;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s3, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x735

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x735;
      assert s1.Peek(5) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s7, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 128
    * Starting at 0x735
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x735 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Push1(s1, 0x06);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap3(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x213;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Swap1(s18);
      var s20 := Swap2(s19);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x213;
      var s22 := Or(s21);
      var s23 := Swap1(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x05);
      var s26 := SLoad(s25);
      var s27 := And(s26);
      var s28 := Push4(s27, 0xf305d719);
      var s29 := SelfBalance(s28);
      var s30 := Address(s29);
      var s31 := Push2(s30, 0x077c);
      assert s31.Peek(0) == 0x77c;
      assert s31.Peek(5) == 0x213;
      var s32 := Dup2(s31);
      var s33 := Push1(s32, 0x01);
      var s34 := Push1(s33, 0x01);
      var s35 := Push1(s34, 0xa0);
      var s36 := Shl(s35);
      var s37 := Sub(s36);
      var s38 := And(s37);
      var s39 := Push0(s38);
      var s40 := Swap1(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s97(s41, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 129
    * Starting at 0x76f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x77c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(1) == 0x77c;
      assert s1.Peek(6) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x20);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Swap1(s5);
      var s7 := Keccak256(s6);
      var s8 := SLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s10, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 130
    * Starting at 0x77c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x078f);
      var s5 := Push0(s4);
      var s6 := SLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x78f;
      assert s11.Peek(10) == 0x213;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s14, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 131
    * Starting at 0x78f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x213;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0xe0);
      var s5 := Dup9(s4);
      var s6 := Swap1(s5);
      var s7 := Shl(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xe0);
      var s11 := Shl(s10);
      assert s11.Peek(12) == 0x213;
      var s12 := Sub(s11);
      var s13 := Not(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0xa0);
      var s20 := Shl(s19);
      var s21 := Sub(s20);
      assert s21.Peek(10) == 0x213;
      var s22 := Swap6(s21);
      var s23 := Dup7(s22);
      var s24 := And(s23);
      var s25 := Push1(s24, 0x04);
      var s26 := Dup3(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x24);
      var s30 := Dup2(s29);
      var s31 := Add(s30);
      assert s31.Peek(10) == 0x213;
      var s32 := Swap5(s31);
      var s33 := Swap1(s32);
      var s34 := Swap5(s33);
      var s35 := MStore(s34);
      var s36 := Push1(s35, 0x44);
      var s37 := Dup5(s36);
      var s38 := Add(s37);
      var s39 := Swap3(s38);
      var s40 := Swap1(s39);
      var s41 := Swap3(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s100(s41, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 132
    * Starting at 0x7c3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      assert s1.Peek(7) == 0x213;
      var s2 := Push1(s1, 0x64);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Swap1(s5);
      var s7 := Swap2(s6);
      var s8 := And(s7);
      var s9 := Push1(s8, 0x84);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x213;
      var s12 := MStore(s11);
      var s13 := TimeStamp(s12);
      var s14 := Push1(s13, 0xa4);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0xc4);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x60);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(6) == 0x213;
      var s22 := MLoad(s21);
      var s23 := Dup1(s22);
      var s24 := Dup4(s23);
      var s25 := Sub(s24);
      var s26 := Dup2(s25);
      var s27 := Dup6(s26);
      var s28 := Dup9(s27);
      var s29 := Gas(s28);
      var s30 := Call(s29);
      var s31 := IsZero(s30);
      assert s31.Peek(5) == 0x213;
      var s32 := Dup1(s31);
      var s33 := IsZero(s32);
      var s34 := Push2(s33, 0x07f5);
      var s35 := JumpI(s34);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s34.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s35, gas - 1)
      else
        ExecuteFromCFGNode_s101(s35, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 133
    * Starting at 0x7ee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 102
    * Segment Id for this node is: 134
    * Starting at 0x7f5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x213;
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
      assert s11.Peek(3) == 0x213;
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
      assert s21.Peek(2) == 0x213;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x081a);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x1114);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s29, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 244
    * Starting at 0x1114
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x81a

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x81a;
      assert s1.Peek(3) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x1126);
      assert s11.Peek(0) == 0x1126;
      assert s11.Peek(7) == 0x81a;
      assert s11.Peek(8) == 0x213;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s12, gas - 1)
      else
        ExecuteFromCFGNode_s104(s12, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 245
    * Starting at 0x1123
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1123 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x81a

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x81a;
      assert s1.Peek(7) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 105
    * Segment Id for this node is: 246
    * Starting at 0x1126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x81a

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x81a;
      assert s1.Peek(6) == 0x213;
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup5(s6);
      var s8 := Add(s7);
      var s9 := MLoad(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x81a;
      assert s11.Peek(6) == 0x213;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup5(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Pop(s16);
      var s18 := Swap3(s17);
      var s19 := Pop(s18);
      var s20 := Swap3(s19);
      var s21 := Pop(s20);
      assert s21.Peek(3) == 0x81a;
      assert s21.Peek(4) == 0x213;
      var s22 := Swap3(s21);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s23, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 135
    * Starting at 0x81a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x213;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x06);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x05);
      var s7 := SLoad(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Push4(s9, 0x095ea7b3);
      var s11 := Push1(s10, 0xe0);
      assert s11.Peek(6) == 0x213;
      var s12 := Shl(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0xa0);
      var s18 := Shl(s17);
      var s19 := Sub(s18);
      var s20 := Swap2(s19);
      var s21 := Dup3(s20);
      assert s21.Peek(6) == 0x213;
      var s22 := And(s21);
      var s23 := Push1(s22, 0x04);
      var s24 := Dup3(s23);
      var s25 := Add(s24);
      var s26 := MStore(s25);
      var s27 := Push0(s26);
      var s28 := Not(s27);
      var s29 := Push1(s28, 0x24);
      var s30 := Dup3(s29);
      var s31 := Add(s30);
      assert s31.Peek(6) == 0x213;
      var s32 := MStore(s31);
      var s33 := Swap2(s32);
      var s34 := And(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Push4(s36, 0x095ea7b3);
      var s38 := Swap1(s37);
      var s39 := Push1(s38, 0x44);
      var s40 := Add(s39);
      var s41 := Push1(s40, 0x20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s107(s41, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 136
    * Starting at 0x856
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x856 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x213;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Sub(s4);
      var s6 := Dup2(s5);
      var s7 := Push0(s6);
      var s8 := Dup8(s7);
      var s9 := Gas(s8);
      var s10 := Call(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(4) == 0x213;
      var s12 := Dup1(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x086f);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s15, gas - 1)
      else
        ExecuteFromCFGNode_s108(s15, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 137
    * Starting at 0x868
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x868 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push0(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 109
    * Segment Id for this node is: 138
    * Starting at 0x86f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x213;
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
      assert s11.Peek(4) == 0x213;
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
      assert s21.Peek(3) == 0x213;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x0893);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x113f);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s28, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 247
    * Starting at 0x113f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x893

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x893;
      assert s1.Peek(3) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x114f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s10, gas - 1)
      else
        ExecuteFromCFGNode_s111(s10, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 248
    * Starting at 0x114c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x893

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(5) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 112
    * Segment Id for this node is: 249
    * Starting at 0x114f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x893

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x893;
      assert s1.Peek(4) == 0x213;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0e2d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s10, gas - 1)
      else
        ExecuteFromCFGNode_s113(s10, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 250
    * Starting at 0x115b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x893

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x893;
      assert s1.Peek(6) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x893

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x893;
      assert s1.Peek(5) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s7, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 139
    * Starting at 0x893
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x893 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x06);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(3) == 0x213;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Or(s13);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s17, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 222
    * Starting at 0x100f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(11) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x101b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s4, gas - 1)
      else
        ExecuteFromCFGNode_s117(s4, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 223
    * Starting at 0x1015
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x5c2;
      assert s1.Peek(9) == 0x5d0;
      assert s1.Peek(10) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s4, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 224
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(11) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s7, gas - 1)
      else
        ExecuteFromCFGNode_s119(s7, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 225
    * Starting at 0x1025
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(13) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x103b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s5, gas - 1)
      else
        ExecuteFromCFGNode_s120(s5, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 226
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1057);
      assert s1.Peek(0) == 0x1057;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(13) == 0x213;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s2, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 231
    * Starting at 0x1057
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1057 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x5c2;
      assert s1.Peek(11) == 0x5d0;
      assert s1.Peek(12) == 0x213;
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
      assert s11.Peek(6) == 0xe2d;
      assert s11.Peek(10) == 0x5c2;
      assert s11.Peek(13) == 0x5d0;
      assert s11.Peek(14) == 0x213;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x107a);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s20, gas - 1)
      else
        ExecuteFromCFGNode_s122(s20, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 232
    * Starting at 0x1072
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1072 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x5c2;
      assert s1.Peek(9) == 0x5d0;
      assert s1.Peek(10) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x0340);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s6, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 233
    * Starting at 0x107a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x5c2

    requires s0.stack[10] == 0x5d0

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x5c2;
      assert s1.Peek(10) == 0x5d0;
      assert s1.Peek(11) == 0x213;
      var s2 := Push2(s1, 0x1084);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0fbf);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 212
    * Starting at 0xfbf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x1084

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x5c2

    requires s0.stack[13] == 0x5d0

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1084;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x5c2;
      assert s1.Peek(13) == 0x5d0;
      assert s1.Peek(14) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s125(s4, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 213
    * Starting at 0xfc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x5c2;
      assert s1.Peek(16) == 0x5d0;
      assert s1.Peek(17) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ff9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s7, gas - 1)
      else
        ExecuteFromCFGNode_s126(s7, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 214
    * Starting at 0xfcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x5c2;
      assert s1.Peek(17) == 0x5d0;
      assert s1.Peek(18) == 0x213;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fdf);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s9, gas - 1)
      else
        ExecuteFromCFGNode_s127(s9, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 215
    * Starting at 0xfd8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0fdf);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x5c2;
      assert s1.Peek(17) == 0x5d0;
      assert s1.Peek(18) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s3, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xfdf

    requires s0.stack[6] == 0x1084

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0x5c2

    requires s0.stack[17] == 0x5d0

    requires s0.stack[18] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x5c2;
      assert s1.Peek(17) == 0x5d0;
      assert s1.Peek(18) == 0x213;
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
      assert s11.Peek(2) == 0xfdf;
      assert s11.Peek(8) == 0x1084;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0x5c2;
      assert s11.Peek(19) == 0x5d0;
      assert s11.Peek(20) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 129
    * Segment Id for this node is: 216
    * Starting at 0xfdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x5c2;
      assert s1.Peek(16) == 0x5d0;
      assert s1.Peek(17) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0fec);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s131(s7, gas - 1)
      else
        ExecuteFromCFGNode_s130(s7, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 217
    * Starting at 0xfe8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x5c2;
      assert s1.Peek(16) == 0x5d0;
      assert s1.Peek(17) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s131(s4, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 218
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x5c2;
      assert s1.Peek(16) == 0x5d0;
      assert s1.Peek(17) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0fc4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s11, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 219
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x5c2

    requires s0.stack[16] == 0x5d0

    requires s0.stack[17] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x5c2;
      assert s1.Peek(16) == 0x5d0;
      assert s1.Peek(17) == 0x213;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s8, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 234
    * Starting at 0x1084
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x5d0

    requires s0.stack[13] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(13) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1097);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s10, gas - 1)
      else
        ExecuteFromCFGNode_s134(s10, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 235
    * Starting at 0x1090
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1090 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x5d0

    requires s0.stack[13] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1097);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x5c2;
      assert s1.Peek(13) == 0x5d0;
      assert s1.Peek(14) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s3, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x1097

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x5c2

    requires s0.stack[13] == 0x5d0

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x5c2;
      assert s1.Peek(13) == 0x5d0;
      assert s1.Peek(14) == 0x213;
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
      assert s11.Peek(2) == 0x1097;
      assert s11.Peek(8) == 0xe2d;
      assert s11.Peek(12) == 0x5c2;
      assert s11.Peek(15) == 0x5d0;
      assert s11.Peek(16) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 136
    * Segment Id for this node is: 236
    * Starting at 0x1097
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1097 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x5d0

    requires s0.stack[13] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(13) == 0x213;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s8, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 228
    * Starting at 0x103b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x5c2;
      assert s1.Peek(11) == 0x5d0;
      assert s1.Peek(12) == 0x213;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x104c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s7, gas - 1)
      else
        ExecuteFromCFGNode_s138(s7, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 229
    * Starting at 0x1045
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1045 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x104c);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(13) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s3, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x104c

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x5c2

    requires s0.stack[12] == 0x5d0

    requires s0.stack[13] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x5c2;
      assert s1.Peek(12) == 0x5d0;
      assert s1.Peek(13) == 0x213;
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
      assert s11.Peek(2) == 0x104c;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0x5c2;
      assert s11.Peek(14) == 0x5d0;
      assert s11.Peek(15) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 140
    * Segment Id for this node is: 230
    * Starting at 0x104c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x5c2;
      assert s1.Peek(11) == 0x5d0;
      assert s1.Peek(12) == 0x213;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x0340);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s8, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 227
    * Starting at 0x1031
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x5c2

    requires s0.stack[11] == 0x5d0

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x5c2;
      assert s1.Peek(11) == 0x5d0;
      assert s1.Peek(12) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 71
    * Starting at 0x2a5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a5 as nat
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
      var s5 := Push2(s4, 0x02b0);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s6, gas - 1)
      else
        ExecuteFromCFGNode_s143(s6, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 72
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
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

  /** Node 144
    * Segment Id for this node is: 73
    * Starting at 0x2b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x015f);
      var s4 := Push2(s3, 0x02bf);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ef1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s8, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 194
    * Starting at 0xef1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2bf

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2bf;
      assert s1.Peek(3) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f02);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s11, gas - 1)
      else
        ExecuteFromCFGNode_s146(s11, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 195
    * Starting at 0xeff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2bf

    requires s0.stack[5] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x2bf;
      assert s1.Peek(6) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 147
    * Segment Id for this node is: 196
    * Starting at 0xf02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2bf

    requires s0.stack[5] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2bf;
      assert s1.Peek(5) == 0x15f;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0f0d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s7, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf0d

    requires s0.stack[7] == 0x2bf

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf0d;
      assert s1.Peek(7) == 0x2bf;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xf0d;
      assert s11.Peek(9) == 0x2bf;
      assert s11.Peek(10) == 0x15f;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s12, gas - 1)
      else
        ExecuteFromCFGNode_s149(s12, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf0d

    requires s0.stack[7] == 0x2bf

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xf0d;
      assert s1.Peek(8) == 0x2bf;
      assert s1.Peek(9) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 150
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf0d

    requires s0.stack[7] == 0x2bf

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf0d;
      assert s1.Peek(7) == 0x2bf;
      assert s1.Peek(8) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s3, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 197
    * Starting at 0xf0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2bf

    requires s0.stack[6] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2bf;
      assert s1.Peek(6) == 0x15f;
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
      assert s11.Peek(1) == 0x2bf;
      assert s11.Peek(4) == 0x15f;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s13, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 74
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15f;
      var s2 := Push2(s1, 0x04f8);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s3, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 109
    * Starting at 0x4f8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x033c);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0a30);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s8, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 152
    * Starting at 0xa30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0a94);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s10, gas - 1)
      else
        ExecuteFromCFGNode_s155(s10, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 153
    * Starting at 0xa3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
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
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
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
      assert s31.Peek(4) == 0x33c;
      assert s31.Peek(8) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s33, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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

  /** Node 157
    * Segment Id for this node is: 154
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0af6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s10, gas - 1)
      else
        ExecuteFromCFGNode_s158(s10, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 155
    * Starting at 0xaa3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
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
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
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
      assert s31.Peek(4) == 0x33c;
      assert s31.Peek(8) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s33, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 156
    * Starting at 0xaf6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x0b57);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s6, gas - 1)
      else
        ExecuteFromCFGNode_s160(s6, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 157
    * Starting at 0xafe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x29);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e7366657220616d6f756e74206d757374206265206772656174657220);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 9, 0x7468616e207a65726f);
      var s24 := Push1(s23, 0xb8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x33c;
      assert s31.Peek(8) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s33, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 158
    * Starting at 0xb57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0b81);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s19, gas - 1)
      else
        ExecuteFromCFGNode_s162(s19, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 159
    * Starting at 0xb6f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := IsZero(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s163(s15, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 160
    * Starting at 0xb81
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d11);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s4, gas - 1)
      else
        ExecuteFromCFGNode_s164(s4, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 161
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x06);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := And(s11);
      var s13 := Eq(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0bb1);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s17, gas - 1)
      else
        ExecuteFromCFGNode_s165(s17, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 162
    * Starting at 0xb9e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := IsZero(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s166(s15, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 163
    * Starting at 0xbb1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0c82);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s4, gas - 1)
      else
        ExecuteFromCFGNode_s167(s4, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 164
    * Starting at 0xbb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x03);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c08);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s7, gas - 1)
      else
        ExecuteFromCFGNode_s168(s7, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 165
    * Starting at 0xbc1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x19);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4578636565647320746865205f6d61785478416d6f756e742e00000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s26, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 166
    * Starting at 0xc08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0c2a);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0xc2a;
      assert s11.Peek(8) == 0x33c;
      assert s11.Peek(12) == 0x15f;
      var s12 := And(s11);
      var s13 := Push0(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x20);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0xc2a;
      assert s21.Peek(8) == 0x33c;
      assert s21.Peek(12) == 0x15f;
      var s22 := Keccak256(s21);
      var s23 := SLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s25, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 167
    * Starting at 0xc2a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x33c

    requires s0.stack[10] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x33c;
      assert s1.Peek(10) == 0x15f;
      var s2 := Push2(s1, 0x0c34);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x115e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s6, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 251
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xc34

    requires s0.stack[7] == 0x33c

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc34;
      assert s1.Peek(7) == 0x33c;
      assert s1.Peek(11) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s10, gas - 1)
      else
        ExecuteFromCFGNode_s172(s10, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 252
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xc34

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xc34;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s3, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xc34

    requires s0.stack[9] == 0x33c

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xc34;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xc34;
      assert s11.Peek(11) == 0x33c;
      assert s11.Peek(15) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 174
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xc34

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc34;
      assert s1.Peek(8) == 0x33c;
      assert s1.Peek(12) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s6, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 168
    * Starting at 0xc34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x33c

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33c;
      assert s1.Peek(9) == 0x15f;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0c82);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s177(s5, gas - 1)
      else
        ExecuteFromCFGNode_s176(s5, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 169
    * Starting at 0xc3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4578636565647320746865206d617857616c6c657453697a652e000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s26, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 170
    * Starting at 0xc82
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Push2(s14, 0x0d11);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s16, gas - 1)
      else
        ExecuteFromCFGNode_s178(s16, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 171
    * Starting at 0xc98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0cb9);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0xcb9;
      assert s11.Peek(7) == 0x33c;
      assert s11.Peek(11) == 0x15f;
      var s12 := Push0(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(1) == 0xcb9;
      assert s21.Peek(7) == 0x33c;
      assert s21.Peek(11) == 0x15f;
      var s22 := SLoad(s21);
      var s23 := Swap1(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s24, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 172
    * Starting at 0xcb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0x33c

    requires s0.stack[10] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x33c;
      assert s1.Peek(10) == 0x15f;
      var s2 := Push2(s1, 0x0cc3);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x115e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s6, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 251
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xcc3

    requires s0.stack[7] == 0x33c

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcc3;
      assert s1.Peek(7) == 0x33c;
      assert s1.Peek(11) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s10, gas - 1)
      else
        ExecuteFromCFGNode_s181(s10, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 252
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xcc3

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xcc3;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s3, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xcc3

    requires s0.stack[9] == 0x33c

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xcc3;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xcc3;
      assert s11.Peek(11) == 0x33c;
      assert s11.Peek(15) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 183
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xcc3

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcc3;
      assert s1.Peek(8) == 0x33c;
      assert s1.Peek(12) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s6, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 173
    * Starting at 0xcc3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x33c

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x33c;
      assert s1.Peek(9) == 0x15f;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0d11);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s5, gas - 1)
      else
        ExecuteFromCFGNode_s185(s5, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 174
    * Starting at 0xcca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4578636565647320746865206d617857616c6c657453697a652e000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s26, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 175
    * Starting at 0xd11
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push2(s19, 0x0d33);
      var s21 := Swap1(s20);
      assert s21.Peek(1) == 0xd33;
      assert s21.Peek(5) == 0x33c;
      assert s21.Peek(9) == 0x15f;
      var s22 := Dup3(s21);
      var s23 := Push2(s22, 0x0dec);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s24, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 183
    * Starting at 0xdec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd33

    requires s0.stack[6] == 0x33c

    requires s0.stack[10] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd33;
      assert s1.Peek(6) == 0x33c;
      assert s1.Peek(10) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0xe2d;
      assert s11.Peek(9) == 0xd33;
      assert s11.Peek(13) == 0x33c;
      assert s11.Peek(17) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x1e);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push32(s18, 0x536166654d6174683a207375627472616374696f6e206f766572666c6f770000);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0xe2d;
      assert s21.Peek(8) == 0xd33;
      assert s21.Peek(12) == 0x33c;
      assert s21.Peek(16) == 0x15f;
      var s22 := Pop(s21);
      var s23 := Push2(s22, 0x0db4);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s24, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 179
    * Starting at 0xdb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0xd33

    requires s0.stack[11] == 0x33c

    requires s0.stack[15] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0xd33;
      assert s1.Peek(11) == 0x33c;
      assert s1.Peek(15) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0dd7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s9, gas - 1)
      else
        ExecuteFromCFGNode_s189(s9, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 180
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0xd33

    requires s0.stack[13] == 0x33c

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0xd33;
      assert s1.Peek(14) == 0x33c;
      assert s1.Peek(18) == 0x15f;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f6;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0xd33;
      assert s11.Peek(15) == 0x33c;
      assert s11.Peek(19) == 0x15f;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0e92);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s14, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 188
    * Starting at 0xe92
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x3f6

    requires s0.stack[7] == 0xe2d

    requires s0.stack[11] == 0xd33

    requires s0.stack[15] == 0x33c

    requires s0.stack[19] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f6;
      assert s1.Peek(7) == 0xe2d;
      assert s1.Peek(11) == 0xd33;
      assert s1.Peek(15) == 0x33c;
      assert s1.Peek(19) == 0x15f;
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
      assert s11.Peek(8) == 0x3f6;
      assert s11.Peek(13) == 0xe2d;
      assert s11.Peek(17) == 0xd33;
      assert s11.Peek(21) == 0x33c;
      assert s11.Peek(25) == 0x15f;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s191(s14, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 189
    * Starting at 0xea1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0xe2d

    requires s0.stack[15] == 0xd33

    requires s0.stack[19] == 0x33c

    requires s0.stack[23] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f6;
      assert s1.Peek(11) == 0xe2d;
      assert s1.Peek(15) == 0xd33;
      assert s1.Peek(19) == 0x33c;
      assert s1.Peek(23) == 0x15f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ebd);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s7, gas - 1)
      else
        ExecuteFromCFGNode_s192(s7, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 190
    * Starting at 0xeaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0xe2d

    requires s0.stack[15] == 0xd33

    requires s0.stack[19] == 0x33c

    requires s0.stack[23] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f6;
      assert s1.Peek(12) == 0xe2d;
      assert s1.Peek(16) == 0xd33;
      assert s1.Peek(20) == 0x33c;
      assert s1.Peek(24) == 0x15f;
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
      assert s11.Peek(8) == 0x3f6;
      assert s11.Peek(13) == 0xe2d;
      assert s11.Peek(17) == 0xd33;
      assert s11.Peek(21) == 0x33c;
      assert s11.Peek(25) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0ea1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s16, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 191
    * Starting at 0xebd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0xe2d

    requires s0.stack[15] == 0xd33

    requires s0.stack[19] == 0x33c

    requires s0.stack[23] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f6;
      assert s1.Peek(11) == 0xe2d;
      assert s1.Peek(15) == 0xd33;
      assert s1.Peek(19) == 0x33c;
      assert s1.Peek(23) == 0x15f;
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
      assert s11.Peek(7) == 0x3f6;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0xd33;
      assert s11.Peek(20) == 0x33c;
      assert s11.Peek(24) == 0x15f;
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
      assert s21.Peek(5) == 0x3f6;
      assert s21.Peek(10) == 0xe2d;
      assert s21.Peek(14) == 0xd33;
      assert s21.Peek(18) == 0x33c;
      assert s21.Peek(22) == 0x15f;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s28, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0xd33

    requires s0.stack[13] == 0x33c

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0xd33;
      assert s1.Peek(13) == 0x33c;
      assert s1.Peek(17) == 0x15f;
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

  /** Node 195
    * Segment Id for this node is: 181
    * Starting at 0xdd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0xd33

    requires s0.stack[13] == 0x33c

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0xd33;
      assert s1.Peek(13) == 0x33c;
      assert s1.Peek(17) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x0de3);
      var s5 := Dup5(s4);
      var s6 := Dup7(s5);
      var s7 := Push2(s6, 0x1171);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s8, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 253
    * Starting at 0x1171
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xde3

    requires s0.stack[8] == 0xe2d

    requires s0.stack[12] == 0xd33

    requires s0.stack[16] == 0x33c

    requires s0.stack[20] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde3;
      assert s1.Peek(8) == 0xe2d;
      assert s1.Peek(12) == 0xd33;
      assert s1.Peek(16) == 0x33c;
      assert s1.Peek(20) == 0x15f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s10, gas - 1)
      else
        ExecuteFromCFGNode_s197(s10, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 254
    * Starting at 0x117d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xde3

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0xd33

    requires s0.stack[17] == 0x33c

    requires s0.stack[21] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0xd33;
      assert s1.Peek(18) == 0x33c;
      assert s1.Peek(22) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s3, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xde3

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0xd33

    requires s0.stack[18] == 0x33c

    requires s0.stack[22] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0xd33;
      assert s1.Peek(18) == 0x33c;
      assert s1.Peek(22) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xde3;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0xd33;
      assert s11.Peek(20) == 0x33c;
      assert s11.Peek(24) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 199
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xde3

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0xd33

    requires s0.stack[17] == 0x33c

    requires s0.stack[21] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0xd33;
      assert s1.Peek(17) == 0x33c;
      assert s1.Peek(21) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s6, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 182
    * Starting at 0xde3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0xd33

    requires s0.stack[14] == 0x33c

    requires s0.stack[18] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0xd33;
      assert s1.Peek(14) == 0x33c;
      assert s1.Peek(18) == 0x15f;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s9, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xd33

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd33;
      assert s1.Peek(8) == 0x33c;
      assert s1.Peek(12) == 0x15f;
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
    * Segment Id for this node is: 176
    * Starting at 0xd33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(7) == 0x33c;
      assert s11.Peek(11) == 0x15f;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Keccak256(s19);
      var s21 := Swap4(s20);
      assert s21.Peek(8) == 0x33c;
      assert s21.Peek(12) == 0x15f;
      var s22 := Swap1(s21);
      var s23 := Swap4(s22);
      var s24 := SStore(s23);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := And(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Keccak256(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(4) == 0x33c;
      assert s31.Peek(8) == 0x15f;
      var s32 := Push2(s31, 0x0d61);
      var s33 := Swap1(s32);
      var s34 := Dup3(s33);
      var s35 := Push2(s34, 0x0e34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s36, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 185
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0xd61

    requires s0.stack[6] == 0x33c

    requires s0.stack[10] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd61;
      assert s1.Peek(6) == 0x33c;
      assert s1.Peek(10) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0e40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x115e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s8, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 251
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xe40

    requires s0.stack[7] == 0xd61

    requires s0.stack[11] == 0x33c

    requires s0.stack[15] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe40;
      assert s1.Peek(7) == 0xd61;
      assert s1.Peek(11) == 0x33c;
      assert s1.Peek(15) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s10, gas - 1)
      else
        ExecuteFromCFGNode_s205(s10, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 252
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xe40

    requires s0.stack[8] == 0xd61

    requires s0.stack[12] == 0x33c

    requires s0.stack[16] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xe40;
      assert s1.Peek(9) == 0xd61;
      assert s1.Peek(13) == 0x33c;
      assert s1.Peek(17) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s3, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xe40

    requires s0.stack[9] == 0xd61

    requires s0.stack[13] == 0x33c

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xe40;
      assert s1.Peek(9) == 0xd61;
      assert s1.Peek(13) == 0x33c;
      assert s1.Peek(17) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xe40;
      assert s11.Peek(11) == 0xd61;
      assert s11.Peek(15) == 0x33c;
      assert s11.Peek(19) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 207
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xe40

    requires s0.stack[8] == 0xd61

    requires s0.stack[12] == 0x33c

    requires s0.stack[16] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe40;
      assert s1.Peek(8) == 0xd61;
      assert s1.Peek(12) == 0x33c;
      assert s1.Peek(16) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s6, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 186
    * Starting at 0xe40
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xd61

    requires s0.stack[9] == 0x33c

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd61;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0e2d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s9, gas - 1)
      else
        ExecuteFromCFGNode_s209(s9, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 187
    * Starting at 0xe4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xd61

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0xd61;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
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
      assert s11.Peek(7) == 0xd61;
      assert s11.Peek(11) == 0x33c;
      assert s11.Peek(15) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x536166654d6174683a206164646974696f6e206f766572666c6f770000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0xd61;
      assert s21.Peek(11) == 0x33c;
      assert s21.Peek(15) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s26, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0xd61

    requires s0.stack[9] == 0x33c

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd61;
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
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

  /** Node 211
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0xd61

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd61;
      assert s1.Peek(8) == 0x33c;
      assert s1.Peek(12) == 0x15f;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s7, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 177
    * Starting at 0xd61
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x33c

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup5(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x33c;
      assert s11.Peek(12) == 0x15f;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x33c;
      assert s21.Peek(12) == 0x15f;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap2(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x33c;
      assert s31.Peek(10) == 0x15f;
      var s32 := Push32(s31, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0a23);
      var s35 := Swap1(s34);
      var s36 := Dup6(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s213(s41, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 178
    * Starting at 0xdb3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0xa23

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s1, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 151
    * Starting at 0xa23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x33c

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x33c;
      assert s1.Peek(11) == 0x15f;
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
      assert s11.Peek(0) == 0x33c;
      assert s11.Peek(4) == 0x15f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s12, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 86
    * Starting at 0x33c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s216(s3, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s6, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 36
    * Starting at 0x15f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15f as nat
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
      var s11 := Push2(s10, 0x0137);
      assert s11.Peek(0) == 0x137;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s12, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x7d1db4a5);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0229);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s6, gas - 1)
      else
        ExecuteFromCFGNode_s219(s6, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 9
    * Starting at 0x63
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x63 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x023e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s236(s5, gas - 1)
      else
        ExecuteFromCFGNode_s220(s5, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 10
    * Starting at 0x6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8f9a55c0);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0264);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s5, gas - 1)
      else
        ExecuteFromCFGNode_s221(s5, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 11
    * Starting at 0x79
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0279);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s223(s5, gas - 1)
      else
        ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 12
    * Starting at 0x84
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
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

  /** Node 223
    * Segment Id for this node is: 68
    * Starting at 0x279
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x279 as nat
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
      var s5 := Push2(s4, 0x0284);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s6, gas - 1)
      else
        ExecuteFromCFGNode_s224(s6, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 69
    * Starting at 0x281
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x281 as nat
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

  /** Node 225
    * Segment Id for this node is: 70
    * Starting at 0x284
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x284 as nat
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
      var s12 := Push1(s11, 0x04);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push4(s14, 0x50455045);
      var s16 := Push1(s15, 0xe0);
      var s17 := Shl(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      var s22 := Push2(s21, 0x012a);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s23, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 30
    * Starting at 0x12a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0137);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0e92);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s8, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 188
    * Starting at 0xe92
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x137;
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
      assert s11.Peek(8) == 0x137;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s228(s14, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 189
    * Starting at 0xea1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x137;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ebd);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s7, gas - 1)
      else
        ExecuteFromCFGNode_s229(s7, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 190
    * Starting at 0xeaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x137;
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
      assert s11.Peek(8) == 0x137;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0ea1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s16, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 191
    * Starting at 0xebd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x137

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x137;
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
      assert s11.Peek(7) == 0x137;
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
      assert s21.Peek(5) == 0x137;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s28, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 65
    * Starting at 0x264
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x264 as nat
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
      var s5 := Push2(s4, 0x026f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s6, gas - 1)
      else
        ExecuteFromCFGNode_s232(s6, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 66
    * Starting at 0x26c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26c as nat
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

  /** Node 233
    * Segment Id for this node is: 67
    * Starting at 0x26f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0183);
      var s4 := Push1(s3, 0x04);
      var s5 := SLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s7, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 40
    * Starting at 0x183
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x183 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x183;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0137);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s10, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 31
    * Starting at 0x137
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x183;
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

  /** Node 236
    * Segment Id for this node is: 62
    * Starting at 0x23e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23e as nat
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
      var s5 := Push2(s4, 0x0249);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s238(s6, gas - 1)
      else
        ExecuteFromCFGNode_s237(s6, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 63
    * Starting at 0x246
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x246 as nat
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

  /** Node 238
    * Segment Id for this node is: 64
    * Starting at 0x249
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x249 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
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
      var s19 := Push2(s18, 0x0137);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s20, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 59
    * Starting at 0x229
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x229 as nat
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
        ExecuteFromCFGNode_s241(s6, gas - 1)
      else
        ExecuteFromCFGNode_s240(s6, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 60
    * Starting at 0x231
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x231 as nat
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

  /** Node 241
    * Segment Id for this node is: 61
    * Starting at 0x234
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x0183);
      var s4 := Push1(s3, 0x03);
      var s5 := SLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s7, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 13
    * Starting at 0x87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x313ce567);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00c2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s385(s6, gas - 1)
      else
        ExecuteFromCFGNode_s243(s6, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s382(s5, gas - 1)
      else
        ExecuteFromCFGNode_s244(s5, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 15
    * Starting at 0x9e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01cb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s371(s5, gas - 1)
      else
        ExecuteFromCFGNode_s245(s5, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 16
    * Starting at 0xa9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x715018a6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01ff);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s365(s5, gas - 1)
      else
        ExecuteFromCFGNode_s246(s5, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 17
    * Starting at 0xb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x751039fc);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0215);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s5, gas - 1)
      else
        ExecuteFromCFGNode_s247(s5, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 18
    * Starting at 0xbf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf as nat
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

  /** Node 248
    * Segment Id for this node is: 56
    * Starting at 0x215
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x215 as nat
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
      var s5 := Push2(s4, 0x0220);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s6, gas - 1)
      else
        ExecuteFromCFGNode_s249(s6, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 57
    * Starting at 0x21d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
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

  /** Node 250
    * Segment Id for this node is: 58
    * Starting at 0x220
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x220 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0213);
      var s4 := Push2(s3, 0x0447);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s5, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 100
    * Starting at 0x447
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x447 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x213;
      var s12 := Push2(s11, 0x0470);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s13, gas - 1)
      else
        ExecuteFromCFGNode_s252(s13, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 101
    * Starting at 0x459
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x459 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x213;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3f6;
      assert s11.Peek(2) == 0x213;
      var s12 := Push2(s11, 0x10c4);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s13, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 102
    * Starting at 0x470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push2(s1, 0x047c);
      var s3 := Push1(s2, 0x09);
      var s4 := Push1(s3, 0x0a);
      var s5 := Push2(s4, 0x109f);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s6, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 237
    * Starting at 0x109f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x47c

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x47c;
      assert s1.Peek(3) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x1001);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s9, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 220
    * Starting at 0x1001
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1001 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xe2d

    requires s0.stack[6] == 0x47c

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x47c;
      assert s1.Peek(7) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x100f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s339(s5, gas - 1)
      else
        ExecuteFromCFGNode_s256(s5, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 221
    * Starting at 0x1008
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1008 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x47c;
      assert s1.Peek(7) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s4, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x47c;
      assert s1.Peek(8) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s6, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x47c

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x47c;
      assert s1.Peek(5) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s7, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 103
    * Starting at 0x47c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Push2(s1, 0x048a);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x05f5e100);
      var s5 := Push2(s4, 0x10ad);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s6, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 238
    * Starting at 0x10ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x48a

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x48a;
      assert s1.Peek(3) == 0x213;
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
      assert s11.Peek(5) == 0x48a;
      assert s11.Peek(6) == 0x213;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0340);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s14, gas - 1)
      else
        ExecuteFromCFGNode_s261(s14, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 239
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x48a

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x48a;
      assert s1.Peek(5) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s3, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0x48a

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x48a;
      assert s1.Peek(5) == 0x213;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0x48a;
      assert s11.Peek(7) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 263
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x48a

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x48a;
      assert s1.Peek(4) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s6, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 104
    * Starting at 0x48a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Push1(s1, 0x03);
      var s3 := SStore(s2);
      var s4 := Push2(s3, 0x0499);
      var s5 := Push1(s4, 0x09);
      var s6 := Push1(s5, 0x0a);
      var s7 := Push2(s6, 0x109f);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s8, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 237
    * Starting at 0x109f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x499

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x499;
      assert s1.Peek(3) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x1001);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s9, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 220
    * Starting at 0x1001
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1001 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0xe2d

    requires s0.stack[6] == 0x499

    requires s0.stack[7] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x499;
      assert s1.Peek(7) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x100f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s313(s5, gas - 1)
      else
        ExecuteFromCFGNode_s267(s5, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 221
    * Starting at 0x1008
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1008 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x499;
      assert s1.Peek(7) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s4, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x499;
      assert s1.Peek(8) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s6, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x499

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x499;
      assert s1.Peek(5) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s7, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 105
    * Starting at 0x499
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x499 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Push2(s1, 0x04a7);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x05f5e100);
      var s5 := Push2(s4, 0x10ad);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s6, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 238
    * Starting at 0x10ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x4a7

    requires s0.stack[3] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4a7;
      assert s1.Peek(3) == 0x213;
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
      assert s11.Peek(5) == 0x4a7;
      assert s11.Peek(6) == 0x213;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0340);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s14, gas - 1)
      else
        ExecuteFromCFGNode_s272(s14, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 239
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x4a7

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x4a7;
      assert s1.Peek(5) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s3, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0x4a7

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x4a7;
      assert s1.Peek(5) == 0x213;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0x4a7;
      assert s11.Peek(7) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 274
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x4a7

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4a7;
      assert s1.Peek(4) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s6, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 106
    * Starting at 0x4a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x213;
      var s2 := Push1(s1, 0x04);
      var s3 := SStore(s2);
      var s4 := Push32(s3, 0x947f344d56e1e8c70dc492fb94c4ddddd490c016aab685f5e7e47b2e85cb44cf);
      var s5 := Push2(s4, 0x04d7);
      var s6 := Push1(s5, 0x09);
      var s7 := Push1(s6, 0x0a);
      var s8 := Push2(s7, 0x109f);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s9, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 237
    * Starting at 0x109f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x4d7

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4d7;
      assert s1.Peek(4) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x1001);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s9, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 220
    * Starting at 0x1001
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1001 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xe2d

    requires s0.stack[6] == 0x4d7

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x4d7;
      assert s1.Peek(8) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x100f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s5, gas - 1)
      else
        ExecuteFromCFGNode_s278(s5, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 221
    * Starting at 0x1008
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1008 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x4d7;
      assert s1.Peek(8) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s4, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x4d7;
      assert s1.Peek(9) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s6, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x4d7

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x4d7;
      assert s1.Peek(6) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s7, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 107
    * Starting at 0x4d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x213;
      var s2 := Push2(s1, 0x04e5);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x05f5e100);
      var s5 := Push2(s4, 0x10ad);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s6, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 238
    * Starting at 0x10ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x4e5

    requires s0.stack[4] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4e5;
      assert s1.Peek(4) == 0x213;
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
      assert s11.Peek(5) == 0x4e5;
      assert s11.Peek(7) == 0x213;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0340);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s14, gas - 1)
      else
        ExecuteFromCFGNode_s283(s14, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 239
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x4e5

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x4e5;
      assert s1.Peek(6) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s3, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0x4e5

    requires s0.stack[6] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x4e5;
      assert s1.Peek(6) == 0x213;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0x4e5;
      assert s11.Peek(8) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 285
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x4e5

    requires s0.stack[5] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4e5;
      assert s1.Peek(5) == 0x213;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 108
    * Starting at 0x4e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x213;
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
      assert s11.Peek(4) == 0x213;
      var s12 := Swap2(s11);
      var s13 := Sub(s12);
      var s14 := Swap1(s13);
      var s15 := Log1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s16, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 222
    * Starting at 0x100f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x4d7;
      assert s1.Peek(9) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x101b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s289(s4, gas - 1)
      else
        ExecuteFromCFGNode_s288(s4, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 223
    * Starting at 0x1015
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x4d7;
      assert s1.Peek(8) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s4, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 224
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x4d7;
      assert s1.Peek(9) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s312(s7, gas - 1)
      else
        ExecuteFromCFGNode_s290(s7, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 225
    * Starting at 0x1025
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x4d7;
      assert s1.Peek(11) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x103b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s308(s5, gas - 1)
      else
        ExecuteFromCFGNode_s291(s5, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 226
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1057);
      assert s1.Peek(0) == 0x1057;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x4d7;
      assert s1.Peek(11) == 0x213;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s292(s2, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 231
    * Starting at 0x1057
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1057 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x4d7;
      assert s1.Peek(10) == 0x213;
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
      assert s11.Peek(6) == 0xe2d;
      assert s11.Peek(10) == 0x4d7;
      assert s11.Peek(12) == 0x213;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x107a);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s20, gas - 1)
      else
        ExecuteFromCFGNode_s293(s20, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 232
    * Starting at 0x1072
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1072 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x4d7;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x0340);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s6, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 233
    * Starting at 0x107a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x4d7

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x4d7;
      assert s1.Peek(9) == 0x213;
      var s2 := Push2(s1, 0x1084);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0fbf);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s295(s6, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 212
    * Starting at 0xfbf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x1084

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x4d7

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1084;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x4d7;
      assert s1.Peek(12) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s296(s4, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 213
    * Starting at 0xfc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x4d7;
      assert s1.Peek(15) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ff9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s303(s7, gas - 1)
      else
        ExecuteFromCFGNode_s297(s7, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 214
    * Starting at 0xfcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x4d7;
      assert s1.Peek(16) == 0x213;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fdf);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s300(s9, gas - 1)
      else
        ExecuteFromCFGNode_s298(s9, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 215
    * Starting at 0xfd8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0fdf);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x4d7;
      assert s1.Peek(16) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s299(s3, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xfdf

    requires s0.stack[6] == 0x1084

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0x4d7

    requires s0.stack[16] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x4d7;
      assert s1.Peek(16) == 0x213;
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
      assert s11.Peek(2) == 0xfdf;
      assert s11.Peek(8) == 0x1084;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0x4d7;
      assert s11.Peek(18) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 300
    * Segment Id for this node is: 216
    * Starting at 0xfdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x4d7;
      assert s1.Peek(15) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0fec);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s302(s7, gas - 1)
      else
        ExecuteFromCFGNode_s301(s7, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 217
    * Starting at 0xfe8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x4d7;
      assert s1.Peek(15) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s302(s4, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 218
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x4d7;
      assert s1.Peek(15) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0fc4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s11, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 219
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x4d7

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x4d7;
      assert s1.Peek(15) == 0x213;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s8, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 234
    * Starting at 0x1084
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x4d7

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x4d7;
      assert s1.Peek(11) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1097);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s307(s10, gas - 1)
      else
        ExecuteFromCFGNode_s305(s10, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 235
    * Starting at 0x1090
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1090 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x4d7

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1097);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x4d7;
      assert s1.Peek(12) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s306(s3, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1097

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x4d7

    requires s0.stack[12] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x4d7;
      assert s1.Peek(12) == 0x213;
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
      assert s11.Peek(2) == 0x1097;
      assert s11.Peek(8) == 0xe2d;
      assert s11.Peek(12) == 0x4d7;
      assert s11.Peek(14) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 307
    * Segment Id for this node is: 236
    * Starting at 0x1097
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1097 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x4d7

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x4d7;
      assert s1.Peek(11) == 0x213;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s280(s8, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 228
    * Starting at 0x103b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x4d7;
      assert s1.Peek(10) == 0x213;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x104c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s311(s7, gas - 1)
      else
        ExecuteFromCFGNode_s309(s7, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 229
    * Starting at 0x1045
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1045 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x104c);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x4d7;
      assert s1.Peek(11) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s3, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x104c

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x4d7

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x4d7;
      assert s1.Peek(11) == 0x213;
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
      assert s11.Peek(2) == 0x104c;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0x4d7;
      assert s11.Peek(13) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 311
    * Segment Id for this node is: 230
    * Starting at 0x104c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x4d7;
      assert s1.Peek(10) == 0x213;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x0340);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s8, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 227
    * Starting at 0x1031
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x4d7

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x4d7;
      assert s1.Peek(10) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s7, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 222
    * Starting at 0x100f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x499;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x101b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s315(s4, gas - 1)
      else
        ExecuteFromCFGNode_s314(s4, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 223
    * Starting at 0x1015
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x499;
      assert s1.Peek(7) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s4, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 224
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x499;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s338(s7, gas - 1)
      else
        ExecuteFromCFGNode_s316(s7, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 225
    * Starting at 0x1025
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x499;
      assert s1.Peek(10) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x103b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s5, gas - 1)
      else
        ExecuteFromCFGNode_s317(s5, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 226
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1057);
      assert s1.Peek(0) == 0x1057;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x499;
      assert s1.Peek(10) == 0x213;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s318(s2, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 231
    * Starting at 0x1057
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1057 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x499;
      assert s1.Peek(9) == 0x213;
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
      assert s11.Peek(6) == 0xe2d;
      assert s11.Peek(10) == 0x499;
      assert s11.Peek(11) == 0x213;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x107a);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s20, gas - 1)
      else
        ExecuteFromCFGNode_s319(s20, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 232
    * Starting at 0x1072
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1072 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x499;
      assert s1.Peek(7) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x0340);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s6, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 233
    * Starting at 0x107a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x499

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x499;
      assert s1.Peek(8) == 0x213;
      var s2 := Push2(s1, 0x1084);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0fbf);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s6, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 212
    * Starting at 0xfbf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1084

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x499

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1084;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x499;
      assert s1.Peek(11) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s322(s4, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 213
    * Starting at 0xfc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x499;
      assert s1.Peek(14) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ff9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s7, gas - 1)
      else
        ExecuteFromCFGNode_s323(s7, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 214
    * Starting at 0xfcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x499;
      assert s1.Peek(15) == 0x213;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fdf);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s326(s9, gas - 1)
      else
        ExecuteFromCFGNode_s324(s9, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 215
    * Starting at 0xfd8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0fdf);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x499;
      assert s1.Peek(15) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s325(s3, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0xfdf

    requires s0.stack[6] == 0x1084

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0x499

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x499;
      assert s1.Peek(15) == 0x213;
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
      assert s11.Peek(2) == 0xfdf;
      assert s11.Peek(8) == 0x1084;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0x499;
      assert s11.Peek(17) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 326
    * Segment Id for this node is: 216
    * Starting at 0xfdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x499;
      assert s1.Peek(14) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0fec);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s328(s7, gas - 1)
      else
        ExecuteFromCFGNode_s327(s7, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 217
    * Starting at 0xfe8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x499;
      assert s1.Peek(14) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s328(s4, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 218
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x499;
      assert s1.Peek(14) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0fc4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s11, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 219
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x499

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x499;
      assert s1.Peek(14) == 0x213;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s330(s8, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 234
    * Starting at 0x1084
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x499

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x499;
      assert s1.Peek(10) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1097);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s333(s10, gas - 1)
      else
        ExecuteFromCFGNode_s331(s10, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 235
    * Starting at 0x1090
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1090 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x499

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1097);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x499;
      assert s1.Peek(11) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s3, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x1097

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x499

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x499;
      assert s1.Peek(11) == 0x213;
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
      assert s11.Peek(2) == 0x1097;
      assert s11.Peek(8) == 0xe2d;
      assert s11.Peek(12) == 0x499;
      assert s11.Peek(13) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 333
    * Segment Id for this node is: 236
    * Starting at 0x1097
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1097 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x499

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x499;
      assert s1.Peek(10) == 0x213;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s8, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 228
    * Starting at 0x103b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x499;
      assert s1.Peek(9) == 0x213;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x104c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s337(s7, gas - 1)
      else
        ExecuteFromCFGNode_s335(s7, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 229
    * Starting at 0x1045
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1045 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x104c);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x499;
      assert s1.Peek(10) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s3, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x104c

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x499

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x499;
      assert s1.Peek(10) == 0x213;
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
      assert s11.Peek(2) == 0x104c;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0x499;
      assert s11.Peek(12) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 337
    * Segment Id for this node is: 230
    * Starting at 0x104c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x499;
      assert s1.Peek(9) == 0x213;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x0340);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s8, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 227
    * Starting at 0x1031
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x499

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x499;
      assert s1.Peek(9) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s7, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 222
    * Starting at 0x100f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x47c;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x101b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s341(s4, gas - 1)
      else
        ExecuteFromCFGNode_s340(s4, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 223
    * Starting at 0x1015
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x47c;
      assert s1.Peek(7) == 0x213;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s4, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 224
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x47c;
      assert s1.Peek(8) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s7, gas - 1)
      else
        ExecuteFromCFGNode_s342(s7, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 225
    * Starting at 0x1025
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x47c;
      assert s1.Peek(10) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x103b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s360(s5, gas - 1)
      else
        ExecuteFromCFGNode_s343(s5, gas - 1)
  }

  /** Node 343
    * Segment Id for this node is: 226
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1057);
      assert s1.Peek(0) == 0x1057;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x47c;
      assert s1.Peek(10) == 0x213;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s2, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 231
    * Starting at 0x1057
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1057 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x47c;
      assert s1.Peek(9) == 0x213;
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
      assert s11.Peek(6) == 0xe2d;
      assert s11.Peek(10) == 0x47c;
      assert s11.Peek(11) == 0x213;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x107a);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s20, gas - 1)
      else
        ExecuteFromCFGNode_s345(s20, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 232
    * Starting at 0x1072
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1072 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x47c;
      assert s1.Peek(7) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x0340);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s6, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 233
    * Starting at 0x107a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x47c

    requires s0.stack[8] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x47c;
      assert s1.Peek(8) == 0x213;
      var s2 := Push2(s1, 0x1084);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0fbf);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s6, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 212
    * Starting at 0xfbf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x1084

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x47c

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1084;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x47c;
      assert s1.Peek(11) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s348(s4, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 213
    * Starting at 0xfc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x47c;
      assert s1.Peek(14) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ff9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s355(s7, gas - 1)
      else
        ExecuteFromCFGNode_s349(s7, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 214
    * Starting at 0xfcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x47c;
      assert s1.Peek(15) == 0x213;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fdf);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s352(s9, gas - 1)
      else
        ExecuteFromCFGNode_s350(s9, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 215
    * Starting at 0xfd8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0fdf);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x47c;
      assert s1.Peek(15) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s3, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0xfdf

    requires s0.stack[6] == 0x1084

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0x47c

    requires s0.stack[15] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x47c;
      assert s1.Peek(15) == 0x213;
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
      assert s11.Peek(2) == 0xfdf;
      assert s11.Peek(8) == 0x1084;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0x47c;
      assert s11.Peek(17) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 352
    * Segment Id for this node is: 216
    * Starting at 0xfdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x47c;
      assert s1.Peek(14) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0fec);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s354(s7, gas - 1)
      else
        ExecuteFromCFGNode_s353(s7, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 217
    * Starting at 0xfe8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x47c;
      assert s1.Peek(14) == 0x213;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s354(s4, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 218
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x47c;
      assert s1.Peek(14) == 0x213;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0fc4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s348(s11, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 219
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x47c

    requires s0.stack[14] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x47c;
      assert s1.Peek(14) == 0x213;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s8, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 234
    * Starting at 0x1084
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x47c

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x47c;
      assert s1.Peek(10) == 0x213;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1097);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s359(s10, gas - 1)
      else
        ExecuteFromCFGNode_s357(s10, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 235
    * Starting at 0x1090
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1090 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x47c

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1097);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x47c;
      assert s1.Peek(11) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s3, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x1097

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x47c

    requires s0.stack[11] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x47c;
      assert s1.Peek(11) == 0x213;
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
      assert s11.Peek(2) == 0x1097;
      assert s11.Peek(8) == 0xe2d;
      assert s11.Peek(12) == 0x47c;
      assert s11.Peek(13) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 359
    * Segment Id for this node is: 236
    * Starting at 0x1097
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1097 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x47c

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x47c;
      assert s1.Peek(10) == 0x213;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s8, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 228
    * Starting at 0x103b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x47c;
      assert s1.Peek(9) == 0x213;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x104c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s363(s7, gas - 1)
      else
        ExecuteFromCFGNode_s361(s7, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 229
    * Starting at 0x1045
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1045 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x104c);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x47c;
      assert s1.Peek(10) == 0x213;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s3, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x104c

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x47c

    requires s0.stack[10] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x47c;
      assert s1.Peek(10) == 0x213;
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
      assert s11.Peek(2) == 0x104c;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0x47c;
      assert s11.Peek(12) == 0x213;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 363
    * Segment Id for this node is: 230
    * Starting at 0x104c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x47c;
      assert s1.Peek(9) == 0x213;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x0340);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s8, gas - 1)
  }

  /** Node 364
    * Segment Id for this node is: 227
    * Starting at 0x1031
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x47c

    requires s0.stack[9] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x47c;
      assert s1.Peek(9) == 0x213;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s7, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 52
    * Starting at 0x1ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ff as nat
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
        ExecuteFromCFGNode_s367(s6, gas - 1)
      else
        ExecuteFromCFGNode_s366(s6, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 53
    * Starting at 0x207
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x207 as nat
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

  /** Node 367
    * Segment Id for this node is: 54
    * Starting at 0x20a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push2(s2, 0x0213);
      var s4 := Push2(s3, 0x03cd);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s5, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 96
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x213;
      var s12 := Push2(s11, 0x03ff);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s370(s13, gas - 1)
      else
        ExecuteFromCFGNode_s369(s13, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 97
    * Starting at 0x3df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x213;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3f6;
      assert s11.Peek(2) == 0x213;
      var s12 := Push2(s11, 0x10c4);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s13, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 99
    * Starting at 0x3ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x213

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(4) == 0x213;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := And(s13);
      var s15 := Swap1(s14);
      var s16 := Push32(s15, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s17 := Swap1(s16);
      var s18 := Dup4(s17);
      var s19 := Swap1(s18);
      var s20 := Log3(s19);
      var s21 := Push0(s20);
      assert s21.Peek(1) == 0x213;
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
      assert s31.Peek(2) == 0x213;
      var s32 := SStore(s31);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s33, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 48
    * Starting at 0x1cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cb as nat
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
      var s5 := Push2(s4, 0x01d6);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s373(s6, gas - 1)
      else
        ExecuteFromCFGNode_s372(s6, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 49
    * Starting at 0x1d3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d3 as nat
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

  /** Node 373
    * Segment Id for this node is: 50
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0183);
      var s4 := Push2(s3, 0x01e5);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0f59);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s374(s8, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 203
    * Starting at 0xf59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1e5

    requires s0.stack[3] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e5;
      assert s1.Peek(3) == 0x183;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0f69);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s376(s10, gas - 1)
      else
        ExecuteFromCFGNode_s375(s10, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 204
    * Starting at 0xf66
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1e5

    requires s0.stack[4] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(4) == 0x1e5;
      assert s1.Peek(5) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 376
    * Segment Id for this node is: 205
    * Starting at 0xf69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1e5

    requires s0.stack[4] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1e5;
      assert s1.Peek(4) == 0x183;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0e2d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s7, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x1e5

    requires s0.stack[7] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x1e5;
      assert s1.Peek(7) == 0x183;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xe2d;
      assert s11.Peek(8) == 0x1e5;
      assert s11.Peek(9) == 0x183;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s12, gas - 1)
      else
        ExecuteFromCFGNode_s378(s12, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x1e5

    requires s0.stack[7] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(7) == 0x1e5;
      assert s1.Peek(8) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 379
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xe2d

    requires s0.stack[6] == 0x1e5

    requires s0.stack[7] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe2d;
      assert s1.Peek(6) == 0x1e5;
      assert s1.Peek(7) == 0x183;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s3, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1e5

    requires s0.stack[5] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1e5;
      assert s1.Peek(5) == 0x183;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s7, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 51
    * Starting at 0x1e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x183;
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
      assert s11.Peek(1) == 0x183;
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
      ExecuteFromCFGNode_s34(s20, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 45
    * Starting at 0x1b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b0 as nat
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
      var s5 := Push2(s4, 0x01bb);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s384(s6, gas - 1)
      else
        ExecuteFromCFGNode_s383(s6, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 46
    * Starting at 0x1b8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b8 as nat
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

  /** Node 384
    * Segment Id for this node is: 47
    * Starting at 0x1bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bb as nat
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
      var s10 := Push2(s9, 0x0137);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s11, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 19
    * Starting at 0xc2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2 as nat
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
      var s5 := Push2(s4, 0x00fd);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s551(s6, gas - 1)
      else
        ExecuteFromCFGNode_s386(s6, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 20
    * Starting at 0xce
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0140);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s533(s5, gas - 1)
      else
        ExecuteFromCFGNode_s387(s5, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 21
    * Starting at 0xd9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x016f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s492(s5, gas - 1)
      else
        ExecuteFromCFGNode_s388(s5, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 22
    * Starting at 0xe4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0191);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s390(s5, gas - 1)
      else
        ExecuteFromCFGNode_s389(s5, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 23
    * Starting at 0xef
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
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

  /** Node 390
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
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
      var s5 := Push2(s4, 0x019c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s392(s6, gas - 1)
      else
        ExecuteFromCFGNode_s391(s6, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 42
    * Starting at 0x199
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x199 as nat
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

  /** Node 392
    * Segment Id for this node is: 43
    * Starting at 0x19c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x015f);
      var s4 := Push2(s3, 0x01ab);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0f1b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s393(s8, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 198
    * Starting at 0xf1b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ab

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ab;
      assert s1.Peek(3) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0f2d);
      assert s11.Peek(0) == 0xf2d;
      assert s11.Peek(7) == 0x1ab;
      assert s11.Peek(8) == 0x15f;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s12, gas - 1)
      else
        ExecuteFromCFGNode_s394(s12, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 199
    * Starting at 0xf2a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1ab

    requires s0.stack[6] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(7) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 395
    * Segment Id for this node is: 200
    * Starting at 0xf2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1ab

    requires s0.stack[6] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ab;
      assert s1.Peek(6) == 0x15f;
      var s2 := Dup4(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0f38);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s7, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf38

    requires s0.stack[8] == 0x1ab

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf38;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(9) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xf38;
      assert s11.Peek(10) == 0x1ab;
      assert s11.Peek(11) == 0x15f;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s398(s12, gas - 1)
      else
        ExecuteFromCFGNode_s397(s12, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf38

    requires s0.stack[8] == 0x1ab

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xf38;
      assert s1.Peek(9) == 0x1ab;
      assert s1.Peek(10) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 398
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf38

    requires s0.stack[8] == 0x1ab

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf38;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(9) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s399(s3, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 201
    * Starting at 0xf38
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf38 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1ab

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(7) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push2(s7, 0x0f48);
      var s9 := Dup2(s8);
      var s10 := Push2(s9, 0x0edd);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s400(s11, gas - 1)
  }

  /** Node 400
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf48

    requires s0.stack[8] == 0x1ab

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf48;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(9) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xf48;
      assert s11.Peek(10) == 0x1ab;
      assert s11.Peek(11) == 0x15f;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s402(s12, gas - 1)
      else
        ExecuteFromCFGNode_s401(s12, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf48

    requires s0.stack[8] == 0x1ab

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xf48;
      assert s1.Peek(9) == 0x1ab;
      assert s1.Peek(10) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 402
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0xf48

    requires s0.stack[8] == 0x1ab

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf48;
      assert s1.Peek(8) == 0x1ab;
      assert s1.Peek(9) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s403(s3, gas - 1)
  }

  /** Node 403
    * Segment Id for this node is: 202
    * Starting at 0xf48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x1ab

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1ab;
      assert s1.Peek(7) == 0x15f;
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
      assert s11.Peek(0) == 0x1ab;
      assert s11.Peek(5) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s404(s16, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 44
    * Starting at 0x1ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15f;
      var s2 := Push2(s1, 0x0366);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s3, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 91
    * Starting at 0x366
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x366 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0372);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0a30);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s406(s8, gas - 1)
  }

  /** Node 406
    * Segment Id for this node is: 152
    * Starting at 0xa30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0a94);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s409(s10, gas - 1)
      else
        ExecuteFromCFGNode_s407(s10, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 153
    * Starting at 0xa3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
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
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(11) == 0x15f;
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
      assert s31.Peek(4) == 0x372;
      assert s31.Peek(9) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s33, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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

  /** Node 409
    * Segment Id for this node is: 154
    * Starting at 0xa94
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0af6);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s411(s10, gas - 1)
      else
        ExecuteFromCFGNode_s410(s10, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 155
    * Starting at 0xaa3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
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
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(11) == 0x15f;
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
      assert s31.Peek(4) == 0x372;
      assert s31.Peek(9) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s33, gas - 1)
  }

  /** Node 411
    * Segment Id for this node is: 156
    * Starting at 0xaf6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x0b57);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s413(s6, gas - 1)
      else
        ExecuteFromCFGNode_s412(s6, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 157
    * Starting at 0xafe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xafe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x29);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e7366657220616d6f756e74206d757374206265206772656174657220);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(11) == 0x15f;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 9, 0x7468616e207a65726f);
      var s24 := Push1(s23, 0xb8);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x372;
      assert s31.Peek(9) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s33, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 158
    * Starting at 0xb57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup5(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x0b81);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s415(s19, gas - 1)
      else
        ExecuteFromCFGNode_s414(s19, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 159
    * Starting at 0xb6f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push0(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := IsZero(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s415(s15, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 160
    * Starting at 0xb81
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb81 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0d11);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s438(s4, gas - 1)
      else
        ExecuteFromCFGNode_s416(s4, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 161
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x06);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := And(s11);
      var s13 := Eq(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0bb1);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s418(s17, gas - 1)
      else
        ExecuteFromCFGNode_s417(s17, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 162
    * Starting at 0xb9e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := IsZero(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s418(s15, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 163
    * Starting at 0xbb1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0c82);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s4, gas - 1)
      else
        ExecuteFromCFGNode_s419(s4, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 164
    * Starting at 0xbb7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x03);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0c08);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s421(s7, gas - 1)
      else
        ExecuteFromCFGNode_s420(s7, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 165
    * Starting at 0xbc1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbc1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x19);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4578636565647320746865205f6d61785478416d6f756e742e00000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(11) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s26, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 166
    * Starting at 0xc08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x04);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0c2a);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0xc2a;
      assert s11.Peek(8) == 0x372;
      assert s11.Peek(13) == 0x15f;
      var s12 := And(s11);
      var s13 := Push0(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0x20);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := Swap1(s20);
      assert s21.Peek(2) == 0xc2a;
      assert s21.Peek(8) == 0x372;
      assert s21.Peek(13) == 0x15f;
      var s22 := Keccak256(s21);
      var s23 := SLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s25, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 167
    * Starting at 0xc2a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc2a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x372

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x372;
      assert s1.Peek(11) == 0x15f;
      var s2 := Push2(s1, 0x0c34);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x115e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s423(s6, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 251
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xc34

    requires s0.stack[7] == 0x372

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc34;
      assert s1.Peek(7) == 0x372;
      assert s1.Peek(12) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s426(s10, gas - 1)
      else
        ExecuteFromCFGNode_s424(s10, gas - 1)
  }

  /** Node 424
    * Segment Id for this node is: 252
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xc34

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xc34;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s3, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xc34

    requires s0.stack[9] == 0x372

    requires s0.stack[14] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xc34;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xc34;
      assert s11.Peek(11) == 0x372;
      assert s11.Peek(16) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 426
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xc34

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc34;
      assert s1.Peek(8) == 0x372;
      assert s1.Peek(13) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s427(s6, gas - 1)
  }

  /** Node 427
    * Segment Id for this node is: 168
    * Starting at 0xc34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x372

    requires s0.stack[10] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x372;
      assert s1.Peek(10) == 0x15f;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0c82);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s429(s5, gas - 1)
      else
        ExecuteFromCFGNode_s428(s5, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 169
    * Starting at 0xc3b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4578636565647320746865206d617857616c6c657453697a652e000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(11) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s26, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 170
    * Starting at 0xc82
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Eq(s13);
      var s15 := Push2(s14, 0x0d11);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s438(s16, gas - 1)
      else
        ExecuteFromCFGNode_s430(s16, gas - 1)
  }

  /** Node 430
    * Segment Id for this node is: 171
    * Starting at 0xc98
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
      var s2 := SLoad(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0cb9);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(1) == 0xcb9;
      assert s11.Peek(7) == 0x372;
      assert s11.Peek(12) == 0x15f;
      var s12 := Push0(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x20);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(1) == 0xcb9;
      assert s21.Peek(7) == 0x372;
      assert s21.Peek(12) == 0x15f;
      var s22 := SLoad(s21);
      var s23 := Swap1(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s24, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 172
    * Starting at 0xcb9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x372

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x372;
      assert s1.Peek(11) == 0x15f;
      var s2 := Push2(s1, 0x0cc3);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x115e);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s6, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 251
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0xcc3

    requires s0.stack[7] == 0x372

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xcc3;
      assert s1.Peek(7) == 0x372;
      assert s1.Peek(12) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s435(s10, gas - 1)
      else
        ExecuteFromCFGNode_s433(s10, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 252
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xcc3

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xcc3;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s434(s3, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xcc3

    requires s0.stack[9] == 0x372

    requires s0.stack[14] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xcc3;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xcc3;
      assert s11.Peek(11) == 0x372;
      assert s11.Peek(16) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 435
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0xcc3

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xcc3;
      assert s1.Peek(8) == 0x372;
      assert s1.Peek(13) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s436(s6, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 173
    * Starting at 0xcc3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x372

    requires s0.stack[10] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x372;
      assert s1.Peek(10) == 0x15f;
      var s2 := Gt(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0d11);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s438(s5, gas - 1)
      else
        ExecuteFromCFGNode_s437(s5, gas - 1)
  }

  /** Node 437
    * Segment Id for this node is: 174
    * Starting at 0xcca
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4578636565647320746865206d617857616c6c657453697a652e000000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x372;
      assert s21.Peek(11) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s26, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 175
    * Starting at 0xd11
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x372

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x372;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x372;
      assert s11.Peek(11) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x20);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := Swap1(s16);
      var s18 := Keccak256(s17);
      var s19 := SLoad(s18);
      var s20 := Push2(s19, 0x0d33);
      var s21 := Swap1(s20);
      assert s21.Peek(1) == 0xd33;
      assert s21.Peek(5) == 0x372;
      assert s21.Peek(10) == 0x15f;
      var s22 := Dup3(s21);
      var s23 := Push2(s22, 0x0dec);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s439(s24, gas - 1)
  }

  /** Node 439
    * Segment Id for this node is: 183
    * Starting at 0xdec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xd33

    requires s0.stack[6] == 0x372

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd33;
      assert s1.Peek(6) == 0x372;
      assert s1.Peek(11) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0xe2d;
      assert s11.Peek(9) == 0xd33;
      assert s11.Peek(13) == 0x372;
      assert s11.Peek(18) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x1e);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push32(s18, 0x536166654d6174683a207375627472616374696f6e206f766572666c6f770000);
      var s20 := Dup2(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0xe2d;
      assert s21.Peek(8) == 0xd33;
      assert s21.Peek(12) == 0x372;
      assert s21.Peek(17) == 0x15f;
      var s22 := Pop(s21);
      var s23 := Push2(s22, 0x0db4);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s24, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 179
    * Starting at 0xdb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0xd33

    requires s0.stack[11] == 0x372

    requires s0.stack[16] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0xd33;
      assert s1.Peek(11) == 0x372;
      assert s1.Peek(16) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0dd7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s447(s9, gas - 1)
      else
        ExecuteFromCFGNode_s441(s9, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 180
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0xd33

    requires s0.stack[13] == 0x372

    requires s0.stack[18] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0xd33;
      assert s1.Peek(14) == 0x372;
      assert s1.Peek(19) == 0x15f;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f6;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0xd33;
      assert s11.Peek(15) == 0x372;
      assert s11.Peek(20) == 0x15f;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0e92);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s442(s14, gas - 1)
  }

  /** Node 442
    * Segment Id for this node is: 188
    * Starting at 0xe92
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x3f6

    requires s0.stack[7] == 0xe2d

    requires s0.stack[11] == 0xd33

    requires s0.stack[15] == 0x372

    requires s0.stack[20] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f6;
      assert s1.Peek(7) == 0xe2d;
      assert s1.Peek(11) == 0xd33;
      assert s1.Peek(15) == 0x372;
      assert s1.Peek(20) == 0x15f;
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
      assert s11.Peek(8) == 0x3f6;
      assert s11.Peek(13) == 0xe2d;
      assert s11.Peek(17) == 0xd33;
      assert s11.Peek(21) == 0x372;
      assert s11.Peek(26) == 0x15f;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s443(s14, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 189
    * Starting at 0xea1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0xe2d

    requires s0.stack[15] == 0xd33

    requires s0.stack[19] == 0x372

    requires s0.stack[24] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f6;
      assert s1.Peek(11) == 0xe2d;
      assert s1.Peek(15) == 0xd33;
      assert s1.Peek(19) == 0x372;
      assert s1.Peek(24) == 0x15f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ebd);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s445(s7, gas - 1)
      else
        ExecuteFromCFGNode_s444(s7, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 190
    * Starting at 0xeaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0xe2d

    requires s0.stack[15] == 0xd33

    requires s0.stack[19] == 0x372

    requires s0.stack[24] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f6;
      assert s1.Peek(12) == 0xe2d;
      assert s1.Peek(16) == 0xd33;
      assert s1.Peek(20) == 0x372;
      assert s1.Peek(25) == 0x15f;
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
      assert s11.Peek(8) == 0x3f6;
      assert s11.Peek(13) == 0xe2d;
      assert s11.Peek(17) == 0xd33;
      assert s11.Peek(21) == 0x372;
      assert s11.Peek(26) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0ea1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s443(s16, gas - 1)
  }

  /** Node 445
    * Segment Id for this node is: 191
    * Starting at 0xebd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0xe2d

    requires s0.stack[15] == 0xd33

    requires s0.stack[19] == 0x372

    requires s0.stack[24] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f6;
      assert s1.Peek(11) == 0xe2d;
      assert s1.Peek(15) == 0xd33;
      assert s1.Peek(19) == 0x372;
      assert s1.Peek(24) == 0x15f;
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
      assert s11.Peek(7) == 0x3f6;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0xd33;
      assert s11.Peek(20) == 0x372;
      assert s11.Peek(25) == 0x15f;
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
      assert s21.Peek(5) == 0x3f6;
      assert s21.Peek(10) == 0xe2d;
      assert s21.Peek(14) == 0xd33;
      assert s21.Peek(18) == 0x372;
      assert s21.Peek(23) == 0x15f;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s446(s28, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0xd33

    requires s0.stack[13] == 0x372

    requires s0.stack[18] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0xd33;
      assert s1.Peek(13) == 0x372;
      assert s1.Peek(18) == 0x15f;
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

  /** Node 447
    * Segment Id for this node is: 181
    * Starting at 0xdd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0xd33

    requires s0.stack[13] == 0x372

    requires s0.stack[18] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0xd33;
      assert s1.Peek(13) == 0x372;
      assert s1.Peek(18) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x0de3);
      var s5 := Dup5(s4);
      var s6 := Dup7(s5);
      var s7 := Push2(s6, 0x1171);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s448(s8, gas - 1)
  }

  /** Node 448
    * Segment Id for this node is: 253
    * Starting at 0x1171
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[2] == 0xde3

    requires s0.stack[8] == 0xe2d

    requires s0.stack[12] == 0xd33

    requires s0.stack[16] == 0x372

    requires s0.stack[21] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde3;
      assert s1.Peek(8) == 0xe2d;
      assert s1.Peek(12) == 0xd33;
      assert s1.Peek(16) == 0x372;
      assert s1.Peek(21) == 0x15f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s451(s10, gas - 1)
      else
        ExecuteFromCFGNode_s449(s10, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 254
    * Starting at 0x117d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xde3

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0xd33

    requires s0.stack[17] == 0x372

    requires s0.stack[22] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0xd33;
      assert s1.Peek(18) == 0x372;
      assert s1.Peek(23) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s450(s3, gas - 1)
  }

  /** Node 450
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xde3

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0xd33

    requires s0.stack[18] == 0x372

    requires s0.stack[23] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0xd33;
      assert s1.Peek(18) == 0x372;
      assert s1.Peek(23) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xde3;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0xd33;
      assert s11.Peek(20) == 0x372;
      assert s11.Peek(25) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 451
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[3] == 0xde3

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0xd33

    requires s0.stack[17] == 0x372

    requires s0.stack[22] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0xd33;
      assert s1.Peek(17) == 0x372;
      assert s1.Peek(22) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s6, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 182
    * Starting at 0xde3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0xd33

    requires s0.stack[14] == 0x372

    requires s0.stack[19] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0xd33;
      assert s1.Peek(14) == 0x372;
      assert s1.Peek(19) == 0x15f;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s9, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd33

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd33;
      assert s1.Peek(8) == 0x372;
      assert s1.Peek(13) == 0x15f;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s7, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 176
    * Starting at 0xd33
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd33 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(7) == 0x372;
      assert s11.Peek(12) == 0x15f;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Keccak256(s19);
      var s21 := Swap4(s20);
      assert s21.Peek(8) == 0x372;
      assert s21.Peek(13) == 0x15f;
      var s22 := Swap1(s21);
      var s23 := Swap4(s22);
      var s24 := SStore(s23);
      var s25 := Swap1(s24);
      var s26 := Dup5(s25);
      var s27 := And(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Keccak256(s29);
      var s31 := SLoad(s30);
      assert s31.Peek(4) == 0x372;
      assert s31.Peek(9) == 0x15f;
      var s32 := Push2(s31, 0x0d61);
      var s33 := Swap1(s32);
      var s34 := Dup3(s33);
      var s35 := Push2(s34, 0x0e34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s36, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 185
    * Starting at 0xe34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xd61

    requires s0.stack[6] == 0x372

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd61;
      assert s1.Peek(6) == 0x372;
      assert s1.Peek(11) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0e40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Push2(s6, 0x115e);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s8, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 251
    * Starting at 0x115e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x115e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xe40

    requires s0.stack[7] == 0xd61

    requires s0.stack[11] == 0x372

    requires s0.stack[16] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe40;
      assert s1.Peek(7) == 0xd61;
      assert s1.Peek(11) == 0x372;
      assert s1.Peek(16) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s459(s10, gas - 1)
      else
        ExecuteFromCFGNode_s457(s10, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 252
    * Starting at 0x116a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xe40

    requires s0.stack[8] == 0xd61

    requires s0.stack[12] == 0x372

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xe40;
      assert s1.Peek(9) == 0xd61;
      assert s1.Peek(13) == 0x372;
      assert s1.Peek(18) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s458(s3, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xe40

    requires s0.stack[9] == 0xd61

    requires s0.stack[13] == 0x372

    requires s0.stack[18] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xe40;
      assert s1.Peek(9) == 0xd61;
      assert s1.Peek(13) == 0x372;
      assert s1.Peek(18) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xe40;
      assert s11.Peek(11) == 0xd61;
      assert s11.Peek(15) == 0x372;
      assert s11.Peek(20) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 459
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xe40

    requires s0.stack[8] == 0xd61

    requires s0.stack[12] == 0x372

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe40;
      assert s1.Peek(8) == 0xd61;
      assert s1.Peek(12) == 0x372;
      assert s1.Peek(17) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s6, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 186
    * Starting at 0xe40
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xd61

    requires s0.stack[9] == 0x372

    requires s0.stack[14] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd61;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup4(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0e2d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s463(s9, gas - 1)
      else
        ExecuteFromCFGNode_s461(s9, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 187
    * Starting at 0xe4b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd61

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0xd61;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
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
      assert s11.Peek(7) == 0xd61;
      assert s11.Peek(11) == 0x372;
      assert s11.Peek(16) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1b);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x536166654d6174683a206164646974696f6e206f766572666c6f770000000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0xd61;
      assert s21.Peek(11) == 0x372;
      assert s21.Peek(16) == 0x15f;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x03f6);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s462(s26, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0xd61

    requires s0.stack[9] == 0x372

    requires s0.stack[14] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd61;
      assert s1.Peek(9) == 0x372;
      assert s1.Peek(14) == 0x15f;
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

  /** Node 463
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0xd61

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd61;
      assert s1.Peek(8) == 0x372;
      assert s1.Peek(13) == 0x15f;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s7, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 177
    * Starting at 0xd61
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x372

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x372;
      assert s1.Peek(9) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup5(s7);
      var s9 := And(s8);
      var s10 := Push0(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x372;
      assert s11.Peek(13) == 0x15f;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0x20);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := Swap1(s19);
      var s21 := Keccak256(s20);
      assert s21.Peek(8) == 0x372;
      assert s21.Peek(13) == 0x15f;
      var s22 := Swap4(s21);
      var s23 := Swap1(s22);
      var s24 := Swap4(s23);
      var s25 := SStore(s24);
      var s26 := Swap2(s25);
      var s27 := MLoad(s26);
      var s28 := Swap1(s27);
      var s29 := Dup6(s28);
      var s30 := And(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(6) == 0x372;
      assert s31.Peek(11) == 0x15f;
      var s32 := Push32(s31, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x0a23);
      var s35 := Swap1(s34);
      var s36 := Dup6(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s465(s41, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 178
    * Starting at 0xdb3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0xa23

    requires s0.stack[8] == 0x372

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s466(s1, gas - 1)
  }

  /** Node 466
    * Segment Id for this node is: 151
    * Starting at 0xa23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x372

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x372;
      assert s1.Peek(12) == 0x15f;
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
      assert s11.Peek(0) == 0x372;
      assert s11.Peek(5) == 0x15f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s12, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 92
    * Starting at 0x372
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x372 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x15f;
      var s2 := Push2(s1, 0x03c3);
      var s3 := Dup5(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x03be);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x60);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x3be;
      assert s11.Peek(6) == 0x3c3;
      assert s11.Peek(11) == 0x15f;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := Push1(s14, 0x28);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x1185);
      var s21 := Push1(s20, 0x28);
      assert s21.Peek(5) == 0x3be;
      assert s21.Peek(8) == 0x3c3;
      assert s21.Peek(13) == 0x15f;
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
      assert s31.Peek(4) == 0x3be;
      assert s31.Peek(7) == 0x3c3;
      assert s31.Peek(12) == 0x15f;
      var s32 := Swap1(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x02);
      var s36 := Push1(s35, 0x20);
      var s37 := Swap1(s36);
      var s38 := Dup2(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x40);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s468(s41, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 93
    * Starting at 0x3ad
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x3be

    requires s0.stack[9] == 0x3c3

    requires s0.stack[14] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x3be;
      assert s1.Peek(10) == 0x3c3;
      assert s1.Peek(15) == 0x15f;
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
      assert s11.Peek(3) == 0x3be;
      assert s11.Peek(6) == 0x3c3;
      assert s11.Peek(11) == 0x15f;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0db4);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s469(s15, gas - 1)
  }

  /** Node 469
    * Segment Id for this node is: 179
    * Starting at 0xdb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x3be

    requires s0.stack[6] == 0x3c3

    requires s0.stack[11] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3be;
      assert s1.Peek(6) == 0x3c3;
      assert s1.Peek(11) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0dd7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s476(s9, gas - 1)
      else
        ExecuteFromCFGNode_s470(s9, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 180
    * Starting at 0xdbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x3be

    requires s0.stack[8] == 0x3c3

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x3be;
      assert s1.Peek(9) == 0x3c3;
      assert s1.Peek(14) == 0x15f;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f6);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f6;
      assert s11.Peek(7) == 0x3be;
      assert s11.Peek(10) == 0x3c3;
      assert s11.Peek(15) == 0x15f;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0e92);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s14, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 188
    * Starting at 0xe92
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x3f6

    requires s0.stack[7] == 0x3be

    requires s0.stack[10] == 0x3c3

    requires s0.stack[15] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f6;
      assert s1.Peek(7) == 0x3be;
      assert s1.Peek(10) == 0x3c3;
      assert s1.Peek(15) == 0x15f;
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
      assert s11.Peek(8) == 0x3f6;
      assert s11.Peek(13) == 0x3be;
      assert s11.Peek(16) == 0x3c3;
      assert s11.Peek(21) == 0x15f;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push0(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s472(s14, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 189
    * Starting at 0xea1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0x3be

    requires s0.stack[14] == 0x3c3

    requires s0.stack[19] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f6;
      assert s1.Peek(11) == 0x3be;
      assert s1.Peek(14) == 0x3c3;
      assert s1.Peek(19) == 0x15f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ebd);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s474(s7, gas - 1)
      else
        ExecuteFromCFGNode_s473(s7, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 190
    * Starting at 0xeaa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0x3be

    requires s0.stack[14] == 0x3c3

    requires s0.stack[19] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f6;
      assert s1.Peek(12) == 0x3be;
      assert s1.Peek(15) == 0x3c3;
      assert s1.Peek(20) == 0x15f;
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
      assert s11.Peek(8) == 0x3f6;
      assert s11.Peek(13) == 0x3be;
      assert s11.Peek(16) == 0x3c3;
      assert s11.Peek(21) == 0x15f;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0ea1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s16, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 191
    * Starting at 0xebd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xebd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f6

    requires s0.stack[11] == 0x3be

    requires s0.stack[14] == 0x3c3

    requires s0.stack[19] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f6;
      assert s1.Peek(11) == 0x3be;
      assert s1.Peek(14) == 0x3c3;
      assert s1.Peek(19) == 0x15f;
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
      assert s11.Peek(7) == 0x3f6;
      assert s11.Peek(12) == 0x3be;
      assert s11.Peek(15) == 0x3c3;
      assert s11.Peek(20) == 0x15f;
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
      assert s21.Peek(5) == 0x3f6;
      assert s21.Peek(10) == 0x3be;
      assert s21.Peek(13) == 0x3c3;
      assert s21.Peek(18) == 0x15f;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s475(s28, gas - 1)
  }

  /** Node 475
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s475(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x3be

    requires s0.stack[8] == 0x3c3

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3be;
      assert s1.Peek(8) == 0x3c3;
      assert s1.Peek(13) == 0x15f;
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

  /** Node 476
    * Segment Id for this node is: 181
    * Starting at 0xdd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s476(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x3be

    requires s0.stack[8] == 0x3c3

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3be;
      assert s1.Peek(8) == 0x3c3;
      assert s1.Peek(13) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Push2(s3, 0x0de3);
      var s5 := Dup5(s4);
      var s6 := Dup7(s5);
      var s7 := Push2(s6, 0x1171);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s477(s8, gas - 1)
  }

  /** Node 477
    * Segment Id for this node is: 253
    * Starting at 0x1171
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s477(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0xde3

    requires s0.stack[8] == 0x3be

    requires s0.stack[11] == 0x3c3

    requires s0.stack[16] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde3;
      assert s1.Peek(8) == 0x3be;
      assert s1.Peek(11) == 0x3c3;
      assert s1.Peek(16) == 0x15f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0340);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s480(s10, gas - 1)
      else
        ExecuteFromCFGNode_s478(s10, gas - 1)
  }

  /** Node 478
    * Segment Id for this node is: 254
    * Starting at 0x117d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s478(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xde3

    requires s0.stack[9] == 0x3be

    requires s0.stack[12] == 0x3c3

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(10) == 0x3be;
      assert s1.Peek(13) == 0x3c3;
      assert s1.Peek(18) == 0x15f;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s479(s3, gas - 1)
  }

  /** Node 479
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s479(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0xde3

    requires s0.stack[10] == 0x3be

    requires s0.stack[13] == 0x3c3

    requires s0.stack[18] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0xde3;
      assert s1.Peek(10) == 0x3be;
      assert s1.Peek(13) == 0x3c3;
      assert s1.Peek(18) == 0x15f;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0xde3;
      assert s11.Peek(12) == 0x3be;
      assert s11.Peek(15) == 0x3c3;
      assert s11.Peek(20) == 0x15f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 480
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s480(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0xde3

    requires s0.stack[9] == 0x3be

    requires s0.stack[12] == 0x3c3

    requires s0.stack[17] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xde3;
      assert s1.Peek(9) == 0x3be;
      assert s1.Peek(12) == 0x3c3;
      assert s1.Peek(17) == 0x15f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s481(s6, gas - 1)
  }

  /** Node 481
    * Segment Id for this node is: 182
    * Starting at 0xde3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s481(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x3be

    requires s0.stack[9] == 0x3c3

    requires s0.stack[14] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3be;
      assert s1.Peek(9) == 0x3c3;
      assert s1.Peek(14) == 0x15f;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s482(s9, gas - 1)
  }

  /** Node 482
    * Segment Id for this node is: 94
    * Starting at 0x3be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s482(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c3

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3c3;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push2(s1, 0x090c);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s483(s3, gas - 1)
  }

  /** Node 483
    * Segment Id for this node is: 145
    * Starting at 0x90c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s483(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c3

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3c3;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x096e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s486(s10, gas - 1)
      else
        ExecuteFromCFGNode_s484(s10, gas - 1)
  }

  /** Node 484
    * Segment Id for this node is: 146
    * Starting at 0x91b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s484(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c3

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3c3;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x3c3;
      assert s11.Peek(11) == 0x15f;
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
      assert s21.Peek(6) == 0x3c3;
      assert s21.Peek(11) == 0x15f;
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
      assert s31.Peek(4) == 0x3c3;
      assert s31.Peek(9) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s33, gas - 1)
  }

  /** Node 485
    * Segment Id for this node is: 98
    * Starting at 0x3f6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s485(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x3c3

    requires s0.stack[9] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3c3;
      assert s1.Peek(9) == 0x15f;
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

  /** Node 486
    * Segment Id for this node is: 147
    * Starting at 0x96e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s486(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c3

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3c3;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x09cf);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s488(s10, gas - 1)
      else
        ExecuteFromCFGNode_s487(s10, gas - 1)
  }

  /** Node 487
    * Segment Id for this node is: 148
    * Starting at 0x97d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s487(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c3

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x3c3;
      assert s1.Peek(9) == 0x15f;
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
      assert s11.Peek(6) == 0x3c3;
      assert s11.Peek(11) == 0x15f;
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
      assert s21.Peek(6) == 0x3c3;
      assert s21.Peek(11) == 0x15f;
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
      assert s31.Peek(4) == 0x3c3;
      assert s31.Peek(9) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s485(s33, gas - 1)
  }

  /** Node 488
    * Segment Id for this node is: 149
    * Starting at 0x9cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s488(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3c3

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3c3;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(7) == 0x3c3;
      assert s11.Peek(12) == 0x15f;
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
      assert s21.Peek(10) == 0x3c3;
      assert s21.Peek(15) == 0x15f;
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
      assert s31.Peek(8) == 0x3c3;
      assert s31.Peek(13) == 0x15f;
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
      ExecuteFromCFGNode_s489(s41, gas - 1)
  }

  /** Node 489
    * Segment Id for this node is: 150
    * Starting at 0x9fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s489(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x3c3

    requires s0.stack[13] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x3c3;
      assert s1.Peek(14) == 0x15f;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s490(s5, gas - 1)
  }

  /** Node 490
    * Segment Id for this node is: 151
    * Starting at 0xa23
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s490(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x3c3

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3c3;
      assert s1.Peek(12) == 0x15f;
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
      assert s11.Peek(0) == 0x3c3;
      assert s11.Peek(5) == 0x15f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s491(s12, gas - 1)
  }

  /** Node 491
    * Segment Id for this node is: 95
    * Starting at 0x3c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s491(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s9, gas - 1)
  }

  /** Node 492
    * Segment Id for this node is: 37
    * Starting at 0x16f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s492(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16f as nat
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
      var s5 := Push2(s4, 0x017a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s494(s6, gas - 1)
      else
        ExecuteFromCFGNode_s493(s6, gas - 1)
  }

  /** Node 493
    * Segment Id for this node is: 38
    * Starting at 0x177
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s493(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
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

  /** Node 494
    * Segment Id for this node is: 39
    * Starting at 0x17a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s494(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0183);
      var s4 := Push2(s3, 0x0346);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s495(s5, gas - 1)
  }

  /** Node 495
    * Segment Id for this node is: 88
    * Starting at 0x346
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s495(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x346 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x183;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0353);
      var s4 := Push1(s3, 0x09);
      var s5 := Push1(s4, 0x0a);
      var s6 := Push2(s5, 0x109f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s496(s7, gas - 1)
  }

  /** Node 496
    * Segment Id for this node is: 237
    * Starting at 0x109f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s496(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x353

    requires s0.stack[4] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x353;
      assert s1.Peek(4) == 0x183;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0e2d);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup5(s4);
      var s6 := And(s5);
      var s7 := Dup4(s6);
      var s8 := Push2(s7, 0x1001);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s497(s9, gas - 1)
  }

  /** Node 497
    * Segment Id for this node is: 220
    * Starting at 0x1001
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s497(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1001 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0xe2d

    requires s0.stack[6] == 0x353

    requires s0.stack[8] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x353;
      assert s1.Peek(8) == 0x183;
      var s2 := Push0(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x100f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s507(s5, gas - 1)
      else
        ExecuteFromCFGNode_s498(s5, gas - 1)
  }

  /** Node 498
    * Segment Id for this node is: 221
    * Starting at 0x1008
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s498(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1008 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x353;
      assert s1.Peek(8) == 0x183;
      var s2 := Push1(s1, 0x01);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s4, gas - 1)
  }

  /** Node 499
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s499(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(9) == 0x183;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s6, gas - 1)
  }

  /** Node 500
    * Segment Id for this node is: 184
    * Starting at 0xe2d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s500(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x353

    requires s0.stack[6] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x353;
      assert s1.Peek(6) == 0x183;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s501(s7, gas - 1)
  }

  /** Node 501
    * Segment Id for this node is: 89
    * Starting at 0x353
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s501(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x183;
      var s2 := Push2(s1, 0x0361);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0x05f5e100);
      var s5 := Push2(s4, 0x10ad);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s502(s6, gas - 1)
  }

  /** Node 502
    * Segment Id for this node is: 238
    * Starting at 0x10ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s502(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x361

    requires s0.stack[4] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x361;
      assert s1.Peek(4) == 0x183;
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
      assert s11.Peek(5) == 0x361;
      assert s11.Peek(7) == 0x183;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0340);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s505(s14, gas - 1)
      else
        ExecuteFromCFGNode_s503(s14, gas - 1)
  }

  /** Node 503
    * Segment Id for this node is: 239
    * Starting at 0x10bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s503(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x361

    requires s0.stack[5] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0340);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x361;
      assert s1.Peek(6) == 0x183;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s504(s3, gas - 1)
  }

  /** Node 504
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s504(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x340

    requires s0.stack[4] == 0x361

    requires s0.stack[6] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x340;
      assert s1.Peek(4) == 0x361;
      assert s1.Peek(6) == 0x183;
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
      assert s11.Peek(2) == 0x340;
      assert s11.Peek(6) == 0x361;
      assert s11.Peek(8) == 0x183;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 505
    * Segment Id for this node is: 87
    * Starting at 0x340
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s505(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x340 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x361

    requires s0.stack[5] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x361;
      assert s1.Peek(5) == 0x183;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s506(s6, gas - 1)
  }

  /** Node 506
    * Segment Id for this node is: 90
    * Starting at 0x361
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s506(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x361 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x183;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 507
    * Segment Id for this node is: 222
    * Starting at 0x100f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s507(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x100f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(9) == 0x183;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x101b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s509(s4, gas - 1)
      else
        ExecuteFromCFGNode_s508(s4, gas - 1)
  }

  /** Node 508
    * Segment Id for this node is: 223
    * Starting at 0x1015
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s508(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1015 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x353;
      assert s1.Peek(8) == 0x183;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0340);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s4, gas - 1)
  }

  /** Node 509
    * Segment Id for this node is: 224
    * Starting at 0x101b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s509(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(9) == 0x183;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x1031);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s532(s7, gas - 1)
      else
        ExecuteFromCFGNode_s510(s7, gas - 1)
  }

  /** Node 510
    * Segment Id for this node is: 225
    * Starting at 0x1025
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s510(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1025 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(11) == 0x183;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x103b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s528(s5, gas - 1)
      else
        ExecuteFromCFGNode_s511(s5, gas - 1)
  }

  /** Node 511
    * Segment Id for this node is: 226
    * Starting at 0x102d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s511(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1057);
      assert s1.Peek(0) == 0x1057;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(11) == 0x183;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s512(s2, gas - 1)
  }

  /** Node 512
    * Segment Id for this node is: 231
    * Starting at 0x1057
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s512(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1057 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(10) == 0x183;
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
      assert s11.Peek(6) == 0xe2d;
      assert s11.Peek(10) == 0x353;
      assert s11.Peek(12) == 0x183;
      var s12 := Lt(s11);
      var s13 := Push1(s12, 0x0b);
      var s14 := Dup5(s13);
      var s15 := Lt(s14);
      var s16 := And(s15);
      var s17 := Or(s16);
      var s18 := IsZero(s17);
      var s19 := Push2(s18, 0x107a);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s514(s20, gas - 1)
      else
        ExecuteFromCFGNode_s513(s20, gas - 1)
  }

  /** Node 513
    * Segment Id for this node is: 232
    * Starting at 0x1072
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s513(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1072 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0xe2d;
      assert s1.Peek(6) == 0x353;
      assert s1.Peek(8) == 0x183;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Exp(s3);
      var s5 := Push2(s4, 0x0340);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s6, gas - 1)
  }

  /** Node 514
    * Segment Id for this node is: 233
    * Starting at 0x107a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s514(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x107a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xe2d

    requires s0.stack[7] == 0x353

    requires s0.stack[9] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe2d;
      assert s1.Peek(7) == 0x353;
      assert s1.Peek(9) == 0x183;
      var s2 := Push2(s1, 0x1084);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0fbf);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s515(s6, gas - 1)
  }

  /** Node 515
    * Segment Id for this node is: 212
    * Starting at 0xfbf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s515(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x1084

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x353

    requires s0.stack[12] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1084;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(12) == 0x183;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s516(s4, gas - 1)
  }

  /** Node 516
    * Segment Id for this node is: 213
    * Starting at 0xfc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s516(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(15) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0ff9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s523(s7, gas - 1)
      else
        ExecuteFromCFGNode_s517(s7, gas - 1)
  }

  /** Node 517
    * Segment Id for this node is: 214
    * Starting at 0xfcd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s517(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfcd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x353;
      assert s1.Peek(16) == 0x183;
      var s2 := Push0(s1);
      var s3 := Not(s2);
      var s4 := Div(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0fdf);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s520(s9, gas - 1)
      else
        ExecuteFromCFGNode_s518(s9, gas - 1)
  }

  /** Node 518
    * Segment Id for this node is: 215
    * Starting at 0xfd8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s518(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0fdf);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x353;
      assert s1.Peek(16) == 0x183;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s519(s3, gas - 1)
  }

  /** Node 519
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s519(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xfdf

    requires s0.stack[6] == 0x1084

    requires s0.stack[10] == 0xe2d

    requires s0.stack[14] == 0x353

    requires s0.stack[16] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xfdf;
      assert s1.Peek(6) == 0x1084;
      assert s1.Peek(10) == 0xe2d;
      assert s1.Peek(14) == 0x353;
      assert s1.Peek(16) == 0x183;
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
      assert s11.Peek(2) == 0xfdf;
      assert s11.Peek(8) == 0x1084;
      assert s11.Peek(12) == 0xe2d;
      assert s11.Peek(16) == 0x353;
      assert s11.Peek(18) == 0x183;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 520
    * Segment Id for this node is: 216
    * Starting at 0xfdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s520(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(15) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := And(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0fec);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s522(s7, gas - 1)
      else
        ExecuteFromCFGNode_s521(s7, gas - 1)
  }

  /** Node 521
    * Segment Id for this node is: 217
    * Starting at 0xfe8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s521(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(15) == 0x183;
      var s2 := Dup2(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s522(s4, gas - 1)
  }

  /** Node 522
    * Segment Id for this node is: 218
    * Starting at 0xfec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s522(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(15) == 0x183;
      var s2 := Swap4(s1);
      var s3 := Dup5(s2);
      var s4 := Shr(s3);
      var s5 := Swap4(s4);
      var s6 := Swap1(s5);
      var s7 := Dup1(s6);
      var s8 := Mul(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0fc4);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s516(s11, gas - 1)
  }

  /** Node 523
    * Segment Id for this node is: 219
    * Starting at 0xff9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s523(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x1084

    requires s0.stack[9] == 0xe2d

    requires s0.stack[13] == 0x353

    requires s0.stack[15] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1084;
      assert s1.Peek(9) == 0xe2d;
      assert s1.Peek(13) == 0x353;
      assert s1.Peek(15) == 0x183;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s524(s8, gas - 1)
  }

  /** Node 524
    * Segment Id for this node is: 234
    * Starting at 0x1084
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s524(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x353

    requires s0.stack[11] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(11) == 0x183;
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Div(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1097);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s527(s10, gas - 1)
      else
        ExecuteFromCFGNode_s525(s10, gas - 1)
  }

  /** Node 525
    * Segment Id for this node is: 235
    * Starting at 0x1090
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s525(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1090 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x353

    requires s0.stack[11] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1097);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(12) == 0x183;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s526(s3, gas - 1)
  }

  /** Node 526
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s526(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1097

    requires s0.stack[6] == 0xe2d

    requires s0.stack[10] == 0x353

    requires s0.stack[12] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1097;
      assert s1.Peek(6) == 0xe2d;
      assert s1.Peek(10) == 0x353;
      assert s1.Peek(12) == 0x183;
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
      assert s11.Peek(2) == 0x1097;
      assert s11.Peek(8) == 0xe2d;
      assert s11.Peek(12) == 0x353;
      assert s11.Peek(14) == 0x183;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 527
    * Segment Id for this node is: 236
    * Starting at 0x1097
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s527(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1097 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x353

    requires s0.stack[11] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(11) == 0x183;
      var s2 := Mul(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s500(s8, gas - 1)
  }

  /** Node 528
    * Segment Id for this node is: 228
    * Starting at 0x103b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s528(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x103b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(10) == 0x183;
      var s2 := Push1(s1, 0xff);
      var s3 := Dup5(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x104c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s531(s7, gas - 1)
      else
        ExecuteFromCFGNode_s529(s7, gas - 1)
  }

  /** Node 529
    * Segment Id for this node is: 229
    * Starting at 0x1045
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s529(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1045 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x104c);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(11) == 0x183;
      var s2 := Push2(s1, 0x0fab);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s530(s3, gas - 1)
  }

  /** Node 530
    * Segment Id for this node is: 211
    * Starting at 0xfab
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s530(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x104c

    requires s0.stack[5] == 0xe2d

    requires s0.stack[9] == 0x353

    requires s0.stack[11] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x104c;
      assert s1.Peek(5) == 0xe2d;
      assert s1.Peek(9) == 0x353;
      assert s1.Peek(11) == 0x183;
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
      assert s11.Peek(2) == 0x104c;
      assert s11.Peek(7) == 0xe2d;
      assert s11.Peek(11) == 0x353;
      assert s11.Peek(13) == 0x183;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 531
    * Segment Id for this node is: 230
    * Starting at 0x104c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s531(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(10) == 0x183;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup3(s4);
      var s6 := Shl(s5);
      var s7 := Push2(s6, 0x0340);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s8, gas - 1)
  }

  /** Node 532
    * Segment Id for this node is: 227
    * Starting at 0x1031
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s532(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1031 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xe2d

    requires s0.stack[8] == 0x353

    requires s0.stack[10] == 0x183

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe2d;
      assert s1.Peek(8) == 0x353;
      assert s1.Peek(10) == 0x183;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0340);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s499(s7, gas - 1)
  }

  /** Node 533
    * Segment Id for this node is: 32
    * Starting at 0x140
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s533(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140 as nat
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
      var s5 := Push2(s4, 0x014b);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s535(s6, gas - 1)
      else
        ExecuteFromCFGNode_s534(s6, gas - 1)
  }

  /** Node 534
    * Segment Id for this node is: 33
    * Starting at 0x148
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s534(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148 as nat
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

  /** Node 535
    * Segment Id for this node is: 34
    * Starting at 0x14b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s535(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x015f);
      var s4 := Push2(s3, 0x015a);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x0ef1);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s536(s8, gas - 1)
  }

  /** Node 536
    * Segment Id for this node is: 194
    * Starting at 0xef1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s536(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x15a

    requires s0.stack[3] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15a;
      assert s1.Peek(3) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0f02);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s538(s11, gas - 1)
      else
        ExecuteFromCFGNode_s537(s11, gas - 1)
  }

  /** Node 537
    * Segment Id for this node is: 195
    * Starting at 0xeff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s537(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x15a

    requires s0.stack[5] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(5) == 0x15a;
      assert s1.Peek(6) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 538
    * Segment Id for this node is: 196
    * Starting at 0xf02
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s538(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x15a

    requires s0.stack[5] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x15a;
      assert s1.Peek(5) == 0x15f;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0f0d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0edd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s539(s7, gas - 1)
  }

  /** Node 539
    * Segment Id for this node is: 192
    * Starting at 0xedd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s539(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xedd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf0d

    requires s0.stack[7] == 0x15a

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf0d;
      assert s1.Peek(7) == 0x15a;
      assert s1.Peek(8) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x0909);
      assert s11.Peek(0) == 0x909;
      assert s11.Peek(3) == 0xf0d;
      assert s11.Peek(9) == 0x15a;
      assert s11.Peek(10) == 0x15f;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s541(s12, gas - 1)
      else
        ExecuteFromCFGNode_s540(s12, gas - 1)
  }

  /** Node 540
    * Segment Id for this node is: 193
    * Starting at 0xeee
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s540(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf0d

    requires s0.stack[7] == 0x15a

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      assert s1.Peek(2) == 0xf0d;
      assert s1.Peek(8) == 0x15a;
      assert s1.Peek(9) == 0x15f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 541
    * Segment Id for this node is: 144
    * Starting at 0x909
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s541(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x909 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xf0d

    requires s0.stack[7] == 0x15a

    requires s0.stack[8] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf0d;
      assert s1.Peek(7) == 0x15a;
      assert s1.Peek(8) == 0x15f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s542(s3, gas - 1)
  }

  /** Node 542
    * Segment Id for this node is: 197
    * Starting at 0xf0d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s542(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x15a

    requires s0.stack[6] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x15a;
      assert s1.Peek(6) == 0x15f;
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
      assert s11.Peek(1) == 0x15a;
      assert s11.Peek(4) == 0x15f;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s543(s13, gas - 1)
  }

  /** Node 543
    * Segment Id for this node is: 35
    * Starting at 0x15a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s543(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15f;
      var s2 := Push2(s1, 0x0330);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s544(s3, gas - 1)
  }

  /** Node 544
    * Segment Id for this node is: 85
    * Starting at 0x330
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s544(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x330 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15f;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x033c);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x090c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s545(s8, gas - 1)
  }

  /** Node 545
    * Segment Id for this node is: 145
    * Starting at 0x90c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s545(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x096e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s547(s10, gas - 1)
      else
        ExecuteFromCFGNode_s546(s10, gas - 1)
  }

  /** Node 546
    * Segment Id for this node is: 146
    * Starting at 0x91b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s546(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
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
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
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
      assert s31.Peek(4) == 0x33c;
      assert s31.Peek(8) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s33, gas - 1)
  }

  /** Node 547
    * Segment Id for this node is: 147
    * Starting at 0x96e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s547(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x96e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x09cf);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s549(s10, gas - 1)
      else
        ExecuteFromCFGNode_s548(s10, gas - 1)
  }

  /** Node 548
    * Segment Id for this node is: 148
    * Starting at 0x97d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s548(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x33c;
      assert s1.Peek(8) == 0x15f;
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
      assert s11.Peek(6) == 0x33c;
      assert s11.Peek(10) == 0x15f;
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
      assert s21.Peek(6) == 0x33c;
      assert s21.Peek(10) == 0x15f;
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
      assert s31.Peek(4) == 0x33c;
      assert s31.Peek(8) == 0x15f;
      var s32 := Push2(s31, 0x03f6);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s33, gas - 1)
  }

  /** Node 549
    * Segment Id for this node is: 149
    * Starting at 0x9cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s549(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x33c

    requires s0.stack[7] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33c;
      assert s1.Peek(7) == 0x15f;
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
      assert s11.Peek(7) == 0x33c;
      assert s11.Peek(11) == 0x15f;
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
      assert s21.Peek(10) == 0x33c;
      assert s21.Peek(14) == 0x15f;
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
      assert s31.Peek(8) == 0x33c;
      assert s31.Peek(12) == 0x15f;
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
      ExecuteFromCFGNode_s550(s41, gas - 1)
  }

  /** Node 550
    * Segment Id for this node is: 150
    * Starting at 0x9fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s550(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x33c

    requires s0.stack[12] == 0x15f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x33c;
      assert s1.Peek(13) == 0x15f;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s214(s5, gas - 1)
  }

  /** Node 551
    * Segment Id for this node is: 27
    * Starting at 0xfd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s551(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfd as nat
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
      var s5 := Push2(s4, 0x0108);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s553(s6, gas - 1)
      else
        ExecuteFromCFGNode_s552(s6, gas - 1)
  }

  /** Node 552
    * Segment Id for this node is: 28
    * Starting at 0x105
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s552(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105 as nat
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

  /** Node 553
    * Segment Id for this node is: 29
    * Starting at 0x108
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s553(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x108 as nat
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
      var s12 := Push1(s11, 0x09);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := PushN(s14, 9, 0x506570654c65506577);
      var s16 := Push1(s15, 0xb8);
      var s17 := Shl(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s226(s21, gas - 1)
  }

  /** Node 554
    * Segment Id for this node is: 24
    * Starting at 0xf2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s554(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x00f9);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s556(s4, gas - 1)
      else
        ExecuteFromCFGNode_s555(s4, gas - 1)
  }

  /** Node 555
    * Segment Id for this node is: 25
    * Starting at 0xf8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s555(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf8 as nat
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

  /** Node 556
    * Segment Id for this node is: 26
    * Starting at 0xf9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s556(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9 as nat
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
