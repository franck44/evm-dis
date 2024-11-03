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
      var s7 := Push2(s6, 0x0043);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s8, gas - 1)
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
      var s6 := Push4(s5, 0x07da68f5);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x004f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s160(s9, gas - 1)
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
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s5, gas - 1)
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
      var s2 := Push4(s1, 0xbe9a6555);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0097);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd4e93292);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x009f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x004a);
      assert s1.Peek(0) == 0x4a;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s6(s2, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 8
    * Starting at 0x4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 7
    * Segment Id for this node is: 18
    * Starting at 0x9f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
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
      var s5 := Push2(s4, 0x00ab);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s9(s6, gas - 1)
      else
        ExecuteFromCFGNode_s8(s6, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 19
    * Starting at 0xa7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa7 as nat
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

  /** Node 9
    * Segment Id for this node is: 20
    * Starting at 0xab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0064);
      var s4 := Push2(s3, 0x0251);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 32
    * Starting at 0x251
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x64;
      var s12 := Push2(s11, 0x02b0);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s13, gas - 1)
      else
        ExecuteFromCFGNode_s11(s13, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 33
    * Starting at 0x264
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x264 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x64;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x17);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f6e6c79206f776e65722063616e207769746864726177000000000000000000);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Swap1(s23);
      var s25 := MLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Swap1(s27);
      var s29 := Sub(s28);
      var s30 := Push1(s29, 0x64);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Revert(s32);
      // Segment is terminal (Revert, Stop or Return)
      s33
  }

  /** Node 12
    * Segment Id for this node is: 34
    * Starting at 0x2b0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push32(s1, 0xcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup3(s8);
      var s10 := Dup2(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Dup3(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x33);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Dup1(s18);
      var s20 := Push2(s19, 0x0723);
      var s21 := Push1(s20, 0x33);
      assert s21.Peek(7) == 0x64;
      var s22 := Swap2(s21);
      var s23 := CodeCopy(s22);
      var s24 := Push1(s23, 0x40);
      var s25 := Add(s24);
      var s26 := Swap2(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Push1(s28, 0x40);
      var s30 := MLoad(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(4) == 0x64;
      var s32 := Swap2(s31);
      var s33 := Sub(s32);
      var s34 := Swap1(s33);
      var s35 := Log1(s34);
      var s36 := Push1(s35, 0x01);
      var s37 := SLoad(s36);
      var s38 := Push1(s37, 0x40);
      var s39 := MLoad(s38);
      var s40 := Push1(s39, 0x01);
      var s41 := Push1(s40, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s13(s41, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 35
    * Starting at 0x306
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x306 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0xa0);
      assert s1.Peek(5) == 0x64;
      var s2 := Shl(s1);
      var s3 := Sub(s2);
      var s4 := Swap1(s3);
      var s5 := Swap2(s4);
      var s6 := And(s5);
      var s7 := Swap1(s6);
      var s8 := SelfBalance(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x08fc);
      assert s11.Peek(5) == 0x64;
      var s12 := Mul(s11);
      var s13 := Swap2(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup2(s14);
      var s16 := Dup2(s15);
      var s17 := Dup2(s16);
      var s18 := Dup6(s17);
      var s19 := Dup9(s18);
      var s20 := Dup9(s19);
      var s21 := Call(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := Swap4(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := IsZero(s26);
      var s28 := Dup1(s27);
      var s29 := IsZero(s28);
      var s30 := Push2(s29, 0x01ac);
      var s31 := JumpI(s30);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s30.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s31, gas - 1)
      else
        ExecuteFromCFGNode_s14(s31, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 36
    * Starting at 0x32b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 15
    * Segment Id for this node is: 26
    * Starting at 0x1ac
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s3, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 12
    * Starting at 0x64
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64 as nat
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

  /** Node 17
    * Segment Id for this node is: 17
    * Starting at 0x97
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0064);
      var s3 := Push2(s2, 0x01be);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s4, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 28
    * Starting at 0x1be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push32(s1, 0xcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup3(s8);
      var s10 := Dup2(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Dup3(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x48);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Dup1(s18);
      var s20 := Push2(s19, 0x0756);
      var s21 := Push1(s20, 0x48);
      assert s21.Peek(7) == 0x64;
      var s22 := Swap2(s21);
      var s23 := CodeCopy(s22);
      var s24 := Push1(s23, 0x60);
      var s25 := Add(s24);
      var s26 := Swap2(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Push1(s28, 0x40);
      var s30 := MLoad(s29);
      var s31 := Dup1(s30);
      assert s31.Peek(4) == 0x64;
      var s32 := Swap2(s31);
      var s33 := Sub(s32);
      var s34 := Swap1(s33);
      var s35 := Log1(s34);
      var s36 := Push2(s35, 0x0219);
      var s37 := Push2(s36, 0x0214);
      var s38 := Push2(s37, 0x0334);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s39, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 37
    * Starting at 0x334
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x334 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x214

    requires s0.stack[1] == 0x219

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x214;
      assert s1.Peek(1) == 0x219;
      assert s1.Peek(2) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x0347);
      var s5 := Push2(s4, 0x0342);
      var s6 := Push2(s5, 0x05c6);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 79
    * Starting at 0x5c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x342

    requires s0.stack[1] == 0x347

    requires s0.stack[4] == 0x214

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x342;
      assert s1.Peek(1) == 0x347;
      assert s1.Peek(4) == 0x214;
      assert s1.Peek(5) == 0x219;
      assert s1.Peek(6) == 0x64;
      var s2 := Push4(s1, 0x090c4718);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s4, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 38
    * Starting at 0x342
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x347

    requires s0.stack[4] == 0x214

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x347;
      assert s1.Peek(4) == 0x214;
      assert s1.Peek(5) == 0x219;
      assert s1.Peek(6) == 0x64;
      var s2 := Push2(s1, 0x05ce);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 80
    * Starting at 0x5ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x347

    requires s0.stack[4] == 0x214

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x347;
      assert s1.Peek(4) == 0x214;
      assert s1.Peek(5) == 0x219;
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x08);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x347;
      assert s11.Peek(8) == 0x214;
      assert s11.Peek(9) == 0x219;
      assert s11.Peek(10) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap2(s15);
      var s17 := Dup3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup3(s20);
      assert s21.Peek(7) == 0x347;
      assert s21.Peek(10) == 0x214;
      assert s21.Peek(11) == 0x219;
      assert s21.Peek(12) == 0x64;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := CallDataSize(s24);
      var s26 := Dup4(s25);
      var s27 := CallDataCopy(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(4) == 0x347;
      assert s31.Peek(7) == 0x214;
      assert s31.Peek(8) == 0x219;
      assert s31.Peek(9) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s23(s34, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 81
    * Starting at 0x5f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x347

    requires s0.stack[7] == 0x214

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(7) == 0x214;
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0651);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s7, gas - 1)
      else
        ExecuteFromCFGNode_s24(s7, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 82
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x347

    requires s0.stack[7] == 0x214

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0f);
      assert s1.Peek(5) == 0x347;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Dup5(s1);
      var s3 := And(s2);
      var s4 := Push1(s3, 0x0a);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0611);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s8, gas - 1)
      else
        ExecuteFromCFGNode_s25(s8, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 83
    * Starting at 0x60b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x347

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x57);
      assert s1.Peek(6) == 0x347;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x0614);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s3, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 85
    * Starting at 0x614
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x347

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x347;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0xff);
      var s3 := And(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shl(s6);
      var s8 := Dup4(s7);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x07);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x347;
      assert s11.Peek(11) == 0x214;
      assert s11.Peek(12) == 0x219;
      assert s11.Peek(13) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x062b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s17, gas - 1)
      else
        ExecuteFromCFGNode_s27(s17, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 86
    * Starting at 0x62a
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x347

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 28
    * Segment Id for this node is: 87
    * Starting at 0x62b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x347

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x347;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(8) == 0x347;
      assert s11.Peek(11) == 0x214;
      assert s11.Peek(12) == 0x219;
      assert s11.Peek(13) == 0x64;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x10);
      var s21 := Dup6(s20);
      assert s21.Peek(7) == 0x347;
      assert s21.Peek(10) == 0x214;
      assert s21.Peek(11) == 0x219;
      assert s21.Peek(12) == 0x64;
      var s22 := Div(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x05f5);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s29, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 84
    * Starting at 0x611
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0x347

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x347;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s2, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 88
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x347

    requires s0.stack[7] == 0x214

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x347;
      assert s1.Peek(7) == 0x214;
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s7, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 39
    * Starting at 0x347
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x347 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x214

    requires s0.stack[4] == 0x219

    requires s0.stack[5] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x214;
      assert s1.Peek(4) == 0x219;
      assert s1.Peek(5) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Push2(s4, 0x0358);
      var s6 := Push4(s5, 0x072988b1);
      var s7 := Push2(s6, 0x05ce);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s8, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 80
    * Starting at 0x5ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x358

    requires s0.stack[5] == 0x214

    requires s0.stack[6] == 0x219

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x358;
      assert s1.Peek(5) == 0x214;
      assert s1.Peek(6) == 0x219;
      assert s1.Peek(7) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x08);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x358;
      assert s11.Peek(9) == 0x214;
      assert s11.Peek(10) == 0x219;
      assert s11.Peek(11) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap2(s15);
      var s17 := Dup3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup3(s20);
      assert s21.Peek(7) == 0x358;
      assert s21.Peek(11) == 0x214;
      assert s21.Peek(12) == 0x219;
      assert s21.Peek(13) == 0x64;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := CallDataSize(s24);
      var s26 := Dup4(s25);
      var s27 := CallDataCopy(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(4) == 0x358;
      assert s31.Peek(8) == 0x214;
      assert s31.Peek(9) == 0x219;
      assert s31.Peek(10) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s33(s34, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 81
    * Starting at 0x5f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x358

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x358;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0651);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s40(s7, gas - 1)
      else
        ExecuteFromCFGNode_s34(s7, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 82
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x358

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0f);
      assert s1.Peek(5) == 0x358;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Dup5(s1);
      var s3 := And(s2);
      var s4 := Push1(s3, 0x0a);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0611);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s8, gas - 1)
      else
        ExecuteFromCFGNode_s35(s8, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 83
    * Starting at 0x60b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x358

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x57);
      assert s1.Peek(6) == 0x358;
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Push2(s1, 0x0614);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 85
    * Starting at 0x614
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x358

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x358;
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0xff);
      var s3 := And(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shl(s6);
      var s8 := Dup4(s7);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x07);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x358;
      assert s11.Peek(12) == 0x214;
      assert s11.Peek(13) == 0x219;
      assert s11.Peek(14) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x062b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s17, gas - 1)
      else
        ExecuteFromCFGNode_s37(s17, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 86
    * Starting at 0x62a
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x358

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 38
    * Segment Id for this node is: 87
    * Starting at 0x62b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[8] == 0x358

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x358;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(8) == 0x358;
      assert s11.Peek(12) == 0x214;
      assert s11.Peek(13) == 0x219;
      assert s11.Peek(14) == 0x64;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x10);
      var s21 := Dup6(s20);
      assert s21.Peek(7) == 0x358;
      assert s21.Peek(11) == 0x214;
      assert s21.Peek(12) == 0x219;
      assert s21.Peek(13) == 0x64;
      var s22 := Div(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x05f5);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s29, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 84
    * Starting at 0x611
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x358

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x358;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s36(s2, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 88
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x358

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x358;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 40
    * Starting at 0x358
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x358 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x214

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x214;
      assert s1.Peek(5) == 0x219;
      assert s1.Peek(6) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Push2(s4, 0x0369);
      var s6 := Push4(s5, 0x09a15c14);
      var s7 := Push2(s6, 0x05ce);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s8, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 80
    * Starting at 0x5ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x369

    requires s0.stack[6] == 0x214

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x369;
      assert s1.Peek(6) == 0x214;
      assert s1.Peek(7) == 0x219;
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x08);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x369;
      assert s11.Peek(10) == 0x214;
      assert s11.Peek(11) == 0x219;
      assert s11.Peek(12) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap2(s15);
      var s17 := Dup3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup3(s20);
      assert s21.Peek(7) == 0x369;
      assert s21.Peek(12) == 0x214;
      assert s21.Peek(13) == 0x219;
      assert s21.Peek(14) == 0x64;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := CallDataSize(s24);
      var s26 := Dup4(s25);
      var s27 := CallDataCopy(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(4) == 0x369;
      assert s31.Peek(9) == 0x214;
      assert s31.Peek(10) == 0x219;
      assert s31.Peek(11) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s43(s34, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 81
    * Starting at 0x5f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x369

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x369;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0651);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s7, gas - 1)
      else
        ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 82
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x369

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0f);
      assert s1.Peek(5) == 0x369;
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Dup5(s1);
      var s3 := And(s2);
      var s4 := Push1(s3, 0x0a);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0611);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s8, gas - 1)
      else
        ExecuteFromCFGNode_s45(s8, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 83
    * Starting at 0x60b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x369

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x57);
      assert s1.Peek(6) == 0x369;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push2(s1, 0x0614);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s3, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 85
    * Starting at 0x614
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x369

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x369;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0xff);
      var s3 := And(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shl(s6);
      var s8 := Dup4(s7);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x07);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x369;
      assert s11.Peek(13) == 0x214;
      assert s11.Peek(14) == 0x219;
      assert s11.Peek(15) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x062b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s17, gas - 1)
      else
        ExecuteFromCFGNode_s47(s17, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 86
    * Starting at 0x62a
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[8] == 0x369

    requires s0.stack[13] == 0x214

    requires s0.stack[14] == 0x219

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 48
    * Segment Id for this node is: 87
    * Starting at 0x62b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[8] == 0x369

    requires s0.stack[13] == 0x214

    requires s0.stack[14] == 0x219

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x369;
      assert s1.Peek(13) == 0x214;
      assert s1.Peek(14) == 0x219;
      assert s1.Peek(15) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(8) == 0x369;
      assert s11.Peek(13) == 0x214;
      assert s11.Peek(14) == 0x219;
      assert s11.Peek(15) == 0x64;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x10);
      var s21 := Dup6(s20);
      assert s21.Peek(7) == 0x369;
      assert s21.Peek(12) == 0x214;
      assert s21.Peek(13) == 0x219;
      assert s21.Peek(14) == 0x64;
      var s22 := Div(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x05f5);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s29, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 84
    * Starting at 0x611
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x369

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x369;
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0x30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s46(s2, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 88
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x369

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x369;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s7, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 41
    * Starting at 0x369
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x369 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x214

    requires s0.stack[6] == 0x219

    requires s0.stack[7] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x214;
      assert s1.Peek(6) == 0x219;
      assert s1.Peek(7) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Push2(s4, 0x037a);
      var s6 := Push4(s5, 0x0e067b22);
      var s7 := Push2(s6, 0x05ce);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s8, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 80
    * Starting at 0x5ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x37a

    requires s0.stack[7] == 0x214

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x37a;
      assert s1.Peek(7) == 0x214;
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x08);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x37a;
      assert s11.Peek(11) == 0x214;
      assert s11.Peek(12) == 0x219;
      assert s11.Peek(13) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap2(s15);
      var s17 := Dup3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup3(s20);
      assert s21.Peek(7) == 0x37a;
      assert s21.Peek(13) == 0x214;
      assert s21.Peek(14) == 0x219;
      assert s21.Peek(15) == 0x64;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := CallDataSize(s24);
      var s26 := Dup4(s25);
      var s27 := CallDataCopy(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(4) == 0x37a;
      assert s31.Peek(10) == 0x214;
      assert s31.Peek(11) == 0x219;
      assert s31.Peek(12) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s53(s34, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 81
    * Starting at 0x5f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x37a

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x37a;
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0651);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s7, gas - 1)
      else
        ExecuteFromCFGNode_s54(s7, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 82
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x37a

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0f);
      assert s1.Peek(5) == 0x37a;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Dup5(s1);
      var s3 := And(s2);
      var s4 := Push1(s3, 0x0a);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0611);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s8, gas - 1)
      else
        ExecuteFromCFGNode_s55(s8, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 83
    * Starting at 0x60b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x37a

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x57);
      assert s1.Peek(6) == 0x37a;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Push2(s1, 0x0614);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s3, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 85
    * Starting at 0x614
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x37a

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x37a;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0xff);
      var s3 := And(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shl(s6);
      var s8 := Dup4(s7);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x07);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x37a;
      assert s11.Peek(14) == 0x214;
      assert s11.Peek(15) == 0x219;
      assert s11.Peek(16) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x062b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s17, gas - 1)
      else
        ExecuteFromCFGNode_s57(s17, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 86
    * Starting at 0x62a
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x37a

    requires s0.stack[14] == 0x214

    requires s0.stack[15] == 0x219

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 58
    * Segment Id for this node is: 87
    * Starting at 0x62b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x37a

    requires s0.stack[14] == 0x214

    requires s0.stack[15] == 0x219

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x37a;
      assert s1.Peek(14) == 0x214;
      assert s1.Peek(15) == 0x219;
      assert s1.Peek(16) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(8) == 0x37a;
      assert s11.Peek(14) == 0x214;
      assert s11.Peek(15) == 0x219;
      assert s11.Peek(16) == 0x64;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x10);
      var s21 := Dup6(s20);
      assert s21.Peek(7) == 0x37a;
      assert s21.Peek(13) == 0x214;
      assert s21.Peek(14) == 0x219;
      assert s21.Peek(15) == 0x64;
      var s22 := Div(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x05f5);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s29, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 84
    * Starting at 0x611
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x37a

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x37a;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s56(s2, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 88
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x37a

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x37a;
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s7, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 42
    * Starting at 0x37a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[6] == 0x214

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x214;
      assert s1.Peek(7) == 0x219;
      assert s1.Peek(8) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Push2(s4, 0x0389);
      var s6 := Push2(s5, 0x0342);
      var s7 := Push2(s6, 0x0658);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s8, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 89
    * Starting at 0x658
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x658 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x342

    requires s0.stack[1] == 0x389

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x342;
      assert s1.Peek(1) == 0x389;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Push4(s1, 0x077204e2);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s4, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 38
    * Starting at 0x342
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x389

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x389;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Push2(s1, 0x05ce);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s3, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 80
    * Starting at 0x5ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x389

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x389;
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x08);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x389;
      assert s11.Peek(12) == 0x214;
      assert s11.Peek(13) == 0x219;
      assert s11.Peek(14) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap2(s15);
      var s17 := Dup3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup3(s20);
      assert s21.Peek(7) == 0x389;
      assert s21.Peek(14) == 0x214;
      assert s21.Peek(15) == 0x219;
      assert s21.Peek(16) == 0x64;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := CallDataSize(s24);
      var s26 := Dup4(s25);
      var s27 := CallDataCopy(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(4) == 0x389;
      assert s31.Peek(11) == 0x214;
      assert s31.Peek(12) == 0x219;
      assert s31.Peek(13) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s34, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 81
    * Starting at 0x5f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x389

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x389;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0651);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s7, gas - 1)
      else
        ExecuteFromCFGNode_s66(s7, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 82
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x389

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0f);
      assert s1.Peek(5) == 0x389;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Dup5(s1);
      var s3 := And(s2);
      var s4 := Push1(s3, 0x0a);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0611);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s8, gas - 1)
      else
        ExecuteFromCFGNode_s67(s8, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 83
    * Starting at 0x60b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x389

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x57);
      assert s1.Peek(6) == 0x389;
      assert s1.Peek(13) == 0x214;
      assert s1.Peek(14) == 0x219;
      assert s1.Peek(15) == 0x64;
      var s2 := Push2(s1, 0x0614);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s3, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 85
    * Starting at 0x614
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x389

    requires s0.stack[13] == 0x214

    requires s0.stack[14] == 0x219

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x389;
      assert s1.Peek(13) == 0x214;
      assert s1.Peek(14) == 0x219;
      assert s1.Peek(15) == 0x64;
      var s2 := Push1(s1, 0xff);
      var s3 := And(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shl(s6);
      var s8 := Dup4(s7);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x07);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x389;
      assert s11.Peek(15) == 0x214;
      assert s11.Peek(16) == 0x219;
      assert s11.Peek(17) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x062b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s17, gas - 1)
      else
        ExecuteFromCFGNode_s69(s17, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 86
    * Starting at 0x62a
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x389

    requires s0.stack[15] == 0x214

    requires s0.stack[16] == 0x219

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 70
    * Segment Id for this node is: 87
    * Starting at 0x62b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x389

    requires s0.stack[15] == 0x214

    requires s0.stack[16] == 0x219

    requires s0.stack[17] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x389;
      assert s1.Peek(15) == 0x214;
      assert s1.Peek(16) == 0x219;
      assert s1.Peek(17) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(8) == 0x389;
      assert s11.Peek(15) == 0x214;
      assert s11.Peek(16) == 0x219;
      assert s11.Peek(17) == 0x64;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x10);
      var s21 := Dup6(s20);
      assert s21.Peek(7) == 0x389;
      assert s21.Peek(14) == 0x214;
      assert s21.Peek(15) == 0x219;
      assert s21.Peek(16) == 0x64;
      var s22 := Div(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x05f5);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s29, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 84
    * Starting at 0x611
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x389

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x389;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s68(s2, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 88
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x389

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x389;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s7, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 43
    * Starting at 0x389
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x389 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x214

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x214;
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Push2(s4, 0x0398);
      var s6 := Push2(s5, 0x0342);
      var s7 := Push2(s6, 0x0660);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s8, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 90
    * Starting at 0x660
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x660 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x342

    requires s0.stack[1] == 0x398

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x342;
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push3(s1, 0x09b0a2);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s4, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 38
    * Starting at 0x342
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x342 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x398

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x05ce);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s3, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 80
    * Starting at 0x5ce
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x398

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x398;
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x08);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Dup2(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x398;
      assert s11.Peek(13) == 0x214;
      assert s11.Peek(14) == 0x219;
      assert s11.Peek(15) == 0x64;
      var s12 := Swap1(s11);
      var s13 := Swap3(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Swap2(s15);
      var s17 := Dup3(s16);
      var s18 := Swap2(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup3(s20);
      assert s21.Peek(7) == 0x398;
      assert s21.Peek(15) == 0x214;
      assert s21.Peek(16) == 0x219;
      assert s21.Peek(17) == 0x64;
      var s22 := Add(s21);
      var s23 := Dup2(s22);
      var s24 := Dup1(s23);
      var s25 := CallDataSize(s24);
      var s26 := Dup4(s25);
      var s27 := CallDataCopy(s26);
      var s28 := Add(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(4) == 0x398;
      assert s31.Peek(12) == 0x214;
      assert s31.Peek(13) == 0x219;
      assert s31.Peek(14) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Pop(s32);
      var s34 := Push1(s33, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s77(s34, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 81
    * Starting at 0x5f5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x398

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x398;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x08);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0651);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s7, gas - 1)
      else
        ExecuteFromCFGNode_s78(s7, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 82
    * Starting at 0x5ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x398

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x0f);
      assert s1.Peek(5) == 0x398;
      assert s1.Peek(13) == 0x214;
      assert s1.Peek(14) == 0x219;
      assert s1.Peek(15) == 0x64;
      var s2 := Dup5(s1);
      var s3 := And(s2);
      var s4 := Push1(s3, 0x0a);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0611);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s8, gas - 1)
      else
        ExecuteFromCFGNode_s79(s8, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 83
    * Starting at 0x60b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x398

    requires s0.stack[13] == 0x214

    requires s0.stack[14] == 0x219

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x57);
      assert s1.Peek(6) == 0x398;
      assert s1.Peek(14) == 0x214;
      assert s1.Peek(15) == 0x219;
      assert s1.Peek(16) == 0x64;
      var s2 := Push2(s1, 0x0614);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s3, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 85
    * Starting at 0x614
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x614 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x398

    requires s0.stack[14] == 0x214

    requires s0.stack[15] == 0x219

    requires s0.stack[16] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x398;
      assert s1.Peek(14) == 0x214;
      assert s1.Peek(15) == 0x219;
      assert s1.Peek(16) == 0x64;
      var s2 := Push1(s1, 0xff);
      var s3 := And(s2);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shl(s6);
      var s8 := Dup4(s7);
      var s9 := Dup4(s8);
      var s10 := Push1(s9, 0x07);
      var s11 := Sub(s10);
      assert s11.Peek(8) == 0x398;
      assert s11.Peek(16) == 0x214;
      assert s11.Peek(17) == 0x219;
      assert s11.Peek(18) == 0x64;
      var s12 := Dup2(s11);
      var s13 := MLoad(s12);
      var s14 := Dup2(s13);
      var s15 := Lt(s14);
      var s16 := Push2(s15, 0x062b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s17, gas - 1)
      else
        ExecuteFromCFGNode_s81(s17, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 86
    * Starting at 0x62a
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x398

    requires s0.stack[16] == 0x214

    requires s0.stack[17] == 0x219

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 82
    * Segment Id for this node is: 87
    * Starting at 0x62b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x398

    requires s0.stack[16] == 0x214

    requires s0.stack[17] == 0x219

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x398;
      assert s1.Peek(16) == 0x214;
      assert s1.Peek(17) == 0x219;
      assert s1.Peek(18) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Not(s10);
      assert s11.Peek(8) == 0x398;
      assert s11.Peek(16) == 0x214;
      assert s11.Peek(17) == 0x219;
      assert s11.Peek(18) == 0x64;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x10);
      var s21 := Dup6(s20);
      assert s21.Peek(7) == 0x398;
      assert s21.Peek(15) == 0x214;
      assert s21.Peek(16) == 0x219;
      assert s21.Peek(17) == 0x64;
      var s22 := Div(s21);
      var s23 := Swap5(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Push1(s25, 0x01);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x05f5);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s29, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 84
    * Starting at 0x611
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x611 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x398

    requires s0.stack[13] == 0x214

    requires s0.stack[14] == 0x219

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x398;
      assert s1.Peek(13) == 0x214;
      assert s1.Peek(14) == 0x219;
      assert s1.Peek(15) == 0x64;
      var s2 := Push1(s1, 0x30);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s2, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 88
    * Starting at 0x651
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x651 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x398

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x398;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s7, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 44
    * Starting at 0x398
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x398 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[8] == 0x214

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x214;
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Push2(s4, 0x03a6);
      var s6 := Dup8(s5);
      var s7 := Dup8(s6);
      var s8 := Push2(s7, 0x0667);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s9, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 91
    * Starting at 0x667
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x667 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x3a6

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3a6;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup4(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(9) == 0x3a6;
      assert s11.Peek(18) == 0x214;
      assert s11.Peek(19) == 0x219;
      assert s11.Peek(20) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Swap1(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := Dup4(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s19, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 92
    * Starting at 0x67e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x3a6

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3a6;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x069d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s6, gas - 1)
      else
        ExecuteFromCFGNode_s88(s6, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 93
    * Starting at 0x687
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x687 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x3a6

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x3a6;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x3a6;
      assert s11.Peek(22) == 0x214;
      assert s11.Peek(23) == 0x219;
      assert s11.Peek(24) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x067e);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s18, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 94
    * Starting at 0x69d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x3a6

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3a6;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(15) == 0x3a6;
      assert s11.Peek(24) == 0x214;
      assert s11.Peek(25) == 0x219;
      assert s11.Peek(26) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(12) == 0x3a6;
      assert s21.Peek(21) == 0x214;
      assert s21.Peek(22) == 0x219;
      assert s21.Peek(23) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup6(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := Add(s28);
      var s30 := Swap3(s29);
      var s31 := Dup6(s30);
      assert s31.Peek(11) == 0x3a6;
      assert s31.Peek(20) == 0x214;
      assert s31.Peek(21) == 0x219;
      assert s31.Peek(22) == 0x64;
      var s32 := Add(s31);
      var s33 := Swap2(s32);
      var s34 := Pop(s33);
      var s35 := Dup1(s34);
      var s36 := Dup4(s35);
      var s37 := Dup4(s36);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s90(s37, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 95
    * Starting at 0x6c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x3a6

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3a6;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x06e5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s6, gas - 1)
      else
        ExecuteFromCFGNode_s91(s6, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 96
    * Starting at 0x6cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x3a6

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x3a6;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x3a6;
      assert s11.Peek(22) == 0x214;
      assert s11.Peek(23) == 0x219;
      assert s11.Peek(24) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x06c6);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s18, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 97
    * Starting at 0x6e5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x3a6

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3a6;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(15) == 0x3a6;
      assert s11.Peek(24) == 0x214;
      assert s11.Peek(25) == 0x219;
      assert s11.Peek(26) == 0x64;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(17) == 0x3a6;
      assert s21.Peek(26) == 0x214;
      assert s21.Peek(27) == 0x219;
      assert s21.Peek(28) == 0x64;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(7) == 0x3a6;
      assert s31.Peek(16) == 0x214;
      assert s31.Peek(17) == 0x219;
      assert s31.Peek(18) == 0x64;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s93(s41, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 98
    * Starting at 0x714
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x714 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x3a6

    requires s0.stack[16] == 0x214

    requires s0.stack[17] == 0x219

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(15) == 0x214;
      assert s1.Peek(16) == 0x219;
      assert s1.Peek(17) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x3a6;
      assert s11.Peek(11) == 0x214;
      assert s11.Peek(12) == 0x219;
      assert s11.Peek(13) == 0x64;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s13, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 45
    * Starting at 0x3a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Push2(s1, 0x03b0);
      var s3 := Dup7(s2);
      var s4 := Dup7(s3);
      var s5 := Push2(s4, 0x0667);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s6, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 91
    * Starting at 0x667
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x667 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x3b0

    requires s0.stack[12] == 0x214

    requires s0.stack[13] == 0x219

    requires s0.stack[14] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3b0;
      assert s1.Peek(12) == 0x214;
      assert s1.Peek(13) == 0x219;
      assert s1.Peek(14) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup4(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(9) == 0x3b0;
      assert s11.Peek(19) == 0x214;
      assert s11.Peek(20) == 0x219;
      assert s11.Peek(21) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Swap1(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := Dup4(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s96(s19, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 92
    * Starting at 0x67e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[12] == 0x3b0

    requires s0.stack[22] == 0x214

    requires s0.stack[23] == 0x219

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3b0;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x069d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s6, gas - 1)
      else
        ExecuteFromCFGNode_s97(s6, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 93
    * Starting at 0x687
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x687 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[12] == 0x3b0

    requires s0.stack[22] == 0x214

    requires s0.stack[23] == 0x219

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x3b0;
      assert s1.Peek(23) == 0x214;
      assert s1.Peek(24) == 0x219;
      assert s1.Peek(25) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x3b0;
      assert s11.Peek(23) == 0x214;
      assert s11.Peek(24) == 0x219;
      assert s11.Peek(25) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x067e);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s18, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 94
    * Starting at 0x69d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[12] == 0x3b0

    requires s0.stack[22] == 0x214

    requires s0.stack[23] == 0x219

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3b0;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(15) == 0x3b0;
      assert s11.Peek(25) == 0x214;
      assert s11.Peek(26) == 0x219;
      assert s11.Peek(27) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(12) == 0x3b0;
      assert s21.Peek(22) == 0x214;
      assert s21.Peek(23) == 0x219;
      assert s21.Peek(24) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup6(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := Add(s28);
      var s30 := Swap3(s29);
      var s31 := Dup6(s30);
      assert s31.Peek(11) == 0x3b0;
      assert s31.Peek(21) == 0x214;
      assert s31.Peek(22) == 0x219;
      assert s31.Peek(23) == 0x64;
      var s32 := Add(s31);
      var s33 := Swap2(s32);
      var s34 := Pop(s33);
      var s35 := Dup1(s34);
      var s36 := Dup4(s35);
      var s37 := Dup4(s36);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s99(s37, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 95
    * Starting at 0x6c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[12] == 0x3b0

    requires s0.stack[22] == 0x214

    requires s0.stack[23] == 0x219

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3b0;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x06e5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s6, gas - 1)
      else
        ExecuteFromCFGNode_s100(s6, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 96
    * Starting at 0x6cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[12] == 0x3b0

    requires s0.stack[22] == 0x214

    requires s0.stack[23] == 0x219

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x3b0;
      assert s1.Peek(23) == 0x214;
      assert s1.Peek(24) == 0x219;
      assert s1.Peek(25) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x3b0;
      assert s11.Peek(23) == 0x214;
      assert s11.Peek(24) == 0x219;
      assert s11.Peek(25) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x06c6);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s18, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 97
    * Starting at 0x6e5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[12] == 0x3b0

    requires s0.stack[22] == 0x214

    requires s0.stack[23] == 0x219

    requires s0.stack[24] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3b0;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(15) == 0x3b0;
      assert s11.Peek(25) == 0x214;
      assert s11.Peek(26) == 0x219;
      assert s11.Peek(27) == 0x64;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(17) == 0x3b0;
      assert s21.Peek(27) == 0x214;
      assert s21.Peek(28) == 0x219;
      assert s21.Peek(29) == 0x64;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(7) == 0x3b0;
      assert s31.Peek(17) == 0x214;
      assert s31.Peek(18) == 0x219;
      assert s31.Peek(19) == 0x64;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s102(s41, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 98
    * Starting at 0x714
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x714 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x3b0

    requires s0.stack[17] == 0x214

    requires s0.stack[18] == 0x219

    requires s0.stack[19] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(6) == 0x3b0;
      assert s1.Peek(16) == 0x214;
      assert s1.Peek(17) == 0x219;
      assert s1.Peek(18) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x3b0;
      assert s11.Peek(12) == 0x214;
      assert s11.Peek(13) == 0x219;
      assert s11.Peek(14) == 0x64;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s13, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 46
    * Starting at 0x3b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x214

    requires s0.stack[11] == 0x219

    requires s0.stack[12] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x214;
      assert s1.Peek(11) == 0x219;
      assert s1.Peek(12) == 0x64;
      var s2 := Push2(s1, 0x03ba);
      var s3 := Dup6(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0667);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 91
    * Starting at 0x667
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x667 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x3ba

    requires s0.stack[13] == 0x214

    requires s0.stack[14] == 0x219

    requires s0.stack[15] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3ba;
      assert s1.Peek(13) == 0x214;
      assert s1.Peek(14) == 0x219;
      assert s1.Peek(15) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup4(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(9) == 0x3ba;
      assert s11.Peek(20) == 0x214;
      assert s11.Peek(21) == 0x219;
      assert s11.Peek(22) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Swap1(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := Dup4(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s105(s19, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 92
    * Starting at 0x67e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[12] == 0x3ba

    requires s0.stack[23] == 0x214

    requires s0.stack[24] == 0x219

    requires s0.stack[25] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3ba;
      assert s1.Peek(23) == 0x214;
      assert s1.Peek(24) == 0x219;
      assert s1.Peek(25) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x069d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s6, gas - 1)
      else
        ExecuteFromCFGNode_s106(s6, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 93
    * Starting at 0x687
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x687 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[12] == 0x3ba

    requires s0.stack[23] == 0x214

    requires s0.stack[24] == 0x219

    requires s0.stack[25] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x3ba;
      assert s1.Peek(24) == 0x214;
      assert s1.Peek(25) == 0x219;
      assert s1.Peek(26) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x3ba;
      assert s11.Peek(24) == 0x214;
      assert s11.Peek(25) == 0x219;
      assert s11.Peek(26) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x067e);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s18, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 94
    * Starting at 0x69d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[12] == 0x3ba

    requires s0.stack[23] == 0x214

    requires s0.stack[24] == 0x219

    requires s0.stack[25] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3ba;
      assert s1.Peek(23) == 0x214;
      assert s1.Peek(24) == 0x219;
      assert s1.Peek(25) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(15) == 0x3ba;
      assert s11.Peek(26) == 0x214;
      assert s11.Peek(27) == 0x219;
      assert s11.Peek(28) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(12) == 0x3ba;
      assert s21.Peek(23) == 0x214;
      assert s21.Peek(24) == 0x219;
      assert s21.Peek(25) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup6(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := Add(s28);
      var s30 := Swap3(s29);
      var s31 := Dup6(s30);
      assert s31.Peek(11) == 0x3ba;
      assert s31.Peek(22) == 0x214;
      assert s31.Peek(23) == 0x219;
      assert s31.Peek(24) == 0x64;
      var s32 := Add(s31);
      var s33 := Swap2(s32);
      var s34 := Pop(s33);
      var s35 := Dup1(s34);
      var s36 := Dup4(s35);
      var s37 := Dup4(s36);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s108(s37, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 95
    * Starting at 0x6c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[12] == 0x3ba

    requires s0.stack[23] == 0x214

    requires s0.stack[24] == 0x219

    requires s0.stack[25] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3ba;
      assert s1.Peek(23) == 0x214;
      assert s1.Peek(24) == 0x219;
      assert s1.Peek(25) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x06e5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s6, gas - 1)
      else
        ExecuteFromCFGNode_s109(s6, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 96
    * Starting at 0x6cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[12] == 0x3ba

    requires s0.stack[23] == 0x214

    requires s0.stack[24] == 0x219

    requires s0.stack[25] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x3ba;
      assert s1.Peek(24) == 0x214;
      assert s1.Peek(25) == 0x219;
      assert s1.Peek(26) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x3ba;
      assert s11.Peek(24) == 0x214;
      assert s11.Peek(25) == 0x219;
      assert s11.Peek(26) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x06c6);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s18, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 97
    * Starting at 0x6e5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[12] == 0x3ba

    requires s0.stack[23] == 0x214

    requires s0.stack[24] == 0x219

    requires s0.stack[25] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x3ba;
      assert s1.Peek(23) == 0x214;
      assert s1.Peek(24) == 0x219;
      assert s1.Peek(25) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(15) == 0x3ba;
      assert s11.Peek(26) == 0x214;
      assert s11.Peek(27) == 0x219;
      assert s11.Peek(28) == 0x64;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(17) == 0x3ba;
      assert s21.Peek(28) == 0x214;
      assert s21.Peek(29) == 0x219;
      assert s21.Peek(30) == 0x64;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(7) == 0x3ba;
      assert s31.Peek(18) == 0x214;
      assert s31.Peek(19) == 0x219;
      assert s31.Peek(20) == 0x64;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s111(s41, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 98
    * Starting at 0x714
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x714 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x3ba

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(6) == 0x3ba;
      assert s1.Peek(17) == 0x214;
      assert s1.Peek(18) == 0x219;
      assert s1.Peek(19) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x3ba;
      assert s11.Peek(13) == 0x214;
      assert s11.Peek(14) == 0x219;
      assert s11.Peek(15) == 0x64;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s13, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 47
    * Starting at 0x3ba
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Dup1(s5);
      var s7 := Dup5(s6);
      var s8 := Dup1(s7);
      var s9 := MLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(16) == 0x214;
      assert s11.Peek(17) == 0x219;
      assert s11.Peek(18) == 0x64;
      var s12 := Add(s11);
      var s13 := Swap1(s12);
      var s14 := Dup1(s13);
      var s15 := Dup4(s14);
      var s16 := Dup4(s15);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s113(s16, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 48
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x03ec);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s6, gas - 1)
      else
        ExecuteFromCFGNode_s114(s6, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 49
    * Starting at 0x3d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(19) == 0x214;
      assert s1.Peek(20) == 0x219;
      assert s1.Peek(21) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(19) == 0x214;
      assert s11.Peek(20) == 0x219;
      assert s11.Peek(21) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x03cd);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s18, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 50
    * Starting at 0x3ec
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(21) == 0x214;
      assert s11.Peek(22) == 0x219;
      assert s11.Peek(23) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(18) == 0x214;
      assert s21.Peek(19) == 0x219;
      assert s21.Peek(20) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup7(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := Add(s28);
      var s30 := Swap3(s29);
      var s31 := Dup7(s30);
      assert s31.Peek(17) == 0x214;
      assert s31.Peek(18) == 0x219;
      assert s31.Peek(19) == 0x64;
      var s32 := Add(s31);
      var s33 := Swap2(s32);
      var s34 := Pop(s33);
      var s35 := Dup1(s34);
      var s36 := Dup4(s35);
      var s37 := Dup4(s36);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s116(s37, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 51
    * Starting at 0x415
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x415 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0434);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s118(s6, gas - 1)
      else
        ExecuteFromCFGNode_s117(s6, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 52
    * Starting at 0x41e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(19) == 0x214;
      assert s1.Peek(20) == 0x219;
      assert s1.Peek(21) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(19) == 0x214;
      assert s11.Peek(20) == 0x219;
      assert s11.Peek(21) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0415);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s18, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 53
    * Starting at 0x434
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(21) == 0x214;
      assert s11.Peek(22) == 0x219;
      assert s11.Peek(23) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(18) == 0x214;
      assert s21.Peek(19) == 0x219;
      assert s21.Peek(20) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup6(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := Add(s28);
      var s30 := Swap3(s29);
      var s31 := Dup6(s30);
      assert s31.Peek(17) == 0x214;
      assert s31.Peek(18) == 0x219;
      assert s31.Peek(19) == 0x64;
      var s32 := Add(s31);
      var s33 := Swap2(s32);
      var s34 := Pop(s33);
      var s35 := Dup1(s34);
      var s36 := Dup4(s35);
      var s37 := Dup4(s36);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s119(s37, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 54
    * Starting at 0x45d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x047c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s6, gas - 1)
      else
        ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 55
    * Starting at 0x466
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(19) == 0x214;
      assert s1.Peek(20) == 0x219;
      assert s1.Peek(21) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(19) == 0x214;
      assert s11.Peek(20) == 0x219;
      assert s11.Peek(21) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x045d);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s18, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 56
    * Starting at 0x47c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(21) == 0x214;
      assert s11.Peek(22) == 0x219;
      assert s11.Peek(23) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(18) == 0x214;
      assert s21.Peek(19) == 0x219;
      assert s21.Peek(20) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x40);
      var s25 := Dup1(s24);
      var s26 := MLoad(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Swap5(s28);
      var s30 := Add(s29);
      var s31 := Dup3(s30);
      assert s31.Peek(18) == 0x214;
      assert s31.Peek(19) == 0x219;
      assert s31.Peek(20) == 0x64;
      var s32 := Dup2(s31);
      var s33 := Sub(s32);
      var s34 := Push1(s33, 0x1f);
      var s35 := Not(s34);
      var s36 := Add(s35);
      var s37 := Dup4(s36);
      var s38 := MStore(s37);
      var s39 := Dup1(s38);
      var s40 := Dup6(s39);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s122(s41, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 57
    * Starting at 0x4ab
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[18] == 0x214

    requires s0.stack[19] == 0x219

    requires s0.stack[20] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(18) == 0x214;
      assert s1.Peek(19) == 0x219;
      assert s1.Peek(20) == 0x64;
      var s2 := Swap5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup5(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x03);
      var s8 := Push1(s7, 0xfc);
      var s9 := Shl(s8);
      var s10 := Swap1(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(18) == 0x214;
      assert s11.Peek(19) == 0x219;
      assert s11.Peek(20) == 0x64;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Swap7(s13);
      var s15 := Pop(s14);
      var s16 := Push2(s15, 0x04cf);
      var s17 := Swap6(s16);
      var s18 := Pop(s17);
      var s19 := Swap1(s18);
      var s20 := Swap4(s19);
      var s21 := Pop(s20);
      assert s21.Peek(4) == 0x4cf;
      assert s21.Peek(13) == 0x214;
      assert s21.Peek(14) == 0x219;
      assert s21.Peek(15) == 0x64;
      var s22 := Dup6(s21);
      var s23 := Swap3(s22);
      var s24 := Pop(s23);
      var s25 := Push2(s24, 0x0667);
      var s26 := Swap2(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s29, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 91
    * Starting at 0x667
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x667 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x4cf

    requires s0.stack[11] == 0x214

    requires s0.stack[12] == 0x219

    requires s0.stack[13] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4cf;
      assert s1.Peek(11) == 0x214;
      assert s1.Peek(12) == 0x219;
      assert s1.Peek(13) == 0x64;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup4(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(9) == 0x4cf;
      assert s11.Peek(18) == 0x214;
      assert s11.Peek(19) == 0x219;
      assert s11.Peek(20) == 0x64;
      var s12 := MLoad(s11);
      var s13 := Swap1(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup1(s16);
      var s18 := Dup4(s17);
      var s19 := Dup4(s18);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s124(s19, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 92
    * Starting at 0x67e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x4cf

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x4cf;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x069d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s6, gas - 1)
      else
        ExecuteFromCFGNode_s125(s6, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 93
    * Starting at 0x687
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x687 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x4cf

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x4cf;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x4cf;
      assert s11.Peek(22) == 0x214;
      assert s11.Peek(23) == 0x219;
      assert s11.Peek(24) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x067e);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s18, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 94
    * Starting at 0x69d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x4cf

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x4cf;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap4(s5);
      var s7 := Dup5(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Exp(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(15) == 0x4cf;
      assert s11.Peek(24) == 0x214;
      assert s11.Peek(25) == 0x219;
      assert s11.Peek(26) == 0x64;
      var s12 := Not(s11);
      var s13 := Add(s12);
      var s14 := Dup1(s13);
      var s15 := Not(s14);
      var s16 := Swap1(s15);
      var s17 := Swap3(s16);
      var s18 := And(s17);
      var s19 := Swap2(s18);
      var s20 := And(s19);
      var s21 := Or(s20);
      assert s21.Peek(12) == 0x4cf;
      assert s21.Peek(21) == 0x214;
      assert s21.Peek(22) == 0x219;
      assert s21.Peek(23) == 0x64;
      var s22 := Swap1(s21);
      var s23 := MStore(s22);
      var s24 := Dup6(s23);
      var s25 := MLoad(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Swap4(s27);
      var s29 := Add(s28);
      var s30 := Swap3(s29);
      var s31 := Dup6(s30);
      assert s31.Peek(11) == 0x4cf;
      assert s31.Peek(20) == 0x214;
      assert s31.Peek(21) == 0x219;
      assert s31.Peek(22) == 0x64;
      var s32 := Add(s31);
      var s33 := Swap2(s32);
      var s34 := Pop(s33);
      var s35 := Dup1(s34);
      var s36 := Dup4(s35);
      var s37 := Dup4(s36);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s127(s37, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 95
    * Starting at 0x6c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x4cf

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x4cf;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x06e5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s6, gas - 1)
      else
        ExecuteFromCFGNode_s128(s6, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 96
    * Starting at 0x6cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x4cf

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(13) == 0x4cf;
      assert s1.Peek(22) == 0x214;
      assert s1.Peek(23) == 0x219;
      assert s1.Peek(24) == 0x64;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Swap1(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap2(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(13) == 0x4cf;
      assert s11.Peek(22) == 0x214;
      assert s11.Peek(23) == 0x219;
      assert s11.Peek(24) == 0x64;
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x06c6);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s18, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 97
    * Starting at 0x6e5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[12] == 0x4cf

    requires s0.stack[21] == 0x214

    requires s0.stack[22] == 0x219

    requires s0.stack[23] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x4cf;
      assert s1.Peek(21) == 0x214;
      assert s1.Peek(22) == 0x219;
      assert s1.Peek(23) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(15) == 0x4cf;
      assert s11.Peek(24) == 0x214;
      assert s11.Peek(25) == 0x219;
      assert s11.Peek(26) == 0x64;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(17) == 0x4cf;
      assert s21.Peek(26) == 0x214;
      assert s21.Peek(27) == 0x219;
      assert s21.Peek(28) == 0x64;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(7) == 0x4cf;
      assert s31.Peek(16) == 0x214;
      assert s31.Peek(17) == 0x219;
      assert s31.Peek(18) == 0x64;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s130(s41, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 98
    * Starting at 0x714
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x714 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x4cf

    requires s0.stack[16] == 0x214

    requires s0.stack[17] == 0x219

    requires s0.stack[18] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(6) == 0x4cf;
      assert s1.Peek(15) == 0x214;
      assert s1.Peek(16) == 0x219;
      assert s1.Peek(17) == 0x64;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x4cf;
      assert s11.Peek(11) == 0x214;
      assert s11.Peek(12) == 0x219;
      assert s11.Peek(13) == 0x64;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s13, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 58
    * Starting at 0x4cf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[9] == 0x214

    requires s0.stack[10] == 0x219

    requires s0.stack[11] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x214;
      assert s1.Peek(10) == 0x219;
      assert s1.Peek(11) == 0x64;
      var s2 := Swap(s1, 8);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(0) == 0x214;
      assert s11.Peek(2) == 0x219;
      assert s11.Peek(3) == 0x64;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s12, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 29
    * Starting at 0x214
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x214 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x219

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x219;
      assert s1.Peek(2) == 0x64;
      var s2 := Push2(s1, 0x04db);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s3, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 59
    * Starting at 0x4db
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x219

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x219;
      assert s1.Peek(2) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Push1(s4, 0x02);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s134(s5, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 60
    * Starting at 0x4e2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x219;
      assert s1.Peek(6) == 0x64;
      var s2 := Push1(s1, 0x2a);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x05be);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s7, gas - 1)
      else
        ExecuteFromCFGNode_s135(s7, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 61
    * Starting at 0x4ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(6) == 0x219;
      assert s1.Peek(7) == 0x64;
      var s2 := Dup3(s1);
      var s3 := Mul(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup4(s6);
      var s8 := Dup3(s7);
      var s9 := Dup2(s8);
      var s10 := MLoad(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(10) == 0x219;
      assert s11.Peek(11) == 0x64;
      var s12 := Lt(s11);
      var s13 := Push2(s12, 0x0500);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s14, gas - 1)
      else
        ExecuteFromCFGNode_s136(s14, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 62
    * Starting at 0x4ff
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 137
    * Segment Id for this node is: 63
    * Starting at 0x500
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x500 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x20);
      var s3 := Add(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shr(s6);
      var s8 := Push1(s7, 0xf8);
      var s9 := Shl(s8);
      var s10 := Push1(s9, 0xf8);
      var s11 := Shr(s10);
      assert s11.Peek(7) == 0x219;
      assert s11.Peek(8) == 0x64;
      var s12 := Push1(s11, 0xff);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x00);
      var s17 := Dup5(s16);
      var s18 := Dup4(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Add(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(10) == 0x219;
      assert s21.Peek(11) == 0x64;
      var s22 := MLoad(s21);
      var s23 := Dup2(s22);
      var s24 := Lt(s23);
      var s25 := Push2(s24, 0x0524);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s139(s26, gas - 1)
      else
        ExecuteFromCFGNode_s138(s26, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 64
    * Starting at 0x523
    * Segment type is: INVALID Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x523 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0); // Invalid instruction:

      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 139
    * Segment Id for this node is: 65
    * Starting at 0x524
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x524 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x219

    requires s0.stack[10] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x219;
      assert s1.Peek(10) == 0x64;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0xf8);
      var s7 := Shr(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Push1(s9, 0x61);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(9) == 0x219;
      assert s11.Peek(10) == 0x64;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Dup4(s15);
      var s17 := And(s16);
      var s18 := Lt(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0565);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s21, gas - 1)
      else
        ExecuteFromCFGNode_s140(s21, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 66
    * Starting at 0x541
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x541 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x41);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x055b);
      assert s11.Peek(0) == 0x55b;
      assert s11.Peek(9) == 0x219;
      assert s11.Peek(10) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s12, gas - 1)
      else
        ExecuteFromCFGNode_s141(s12, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 67
    * Starting at 0x553
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x553 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x30);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup3(s1);
      var s3 := Sub(s2);
      var s4 := Push2(s3, 0x0560);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s5, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 69
    * Starting at 0x560
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x560 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x056a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s3, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 71
    * Starting at 0x56a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x56a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x61);
      var s5 := Dup2(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(9) == 0x219;
      assert s11.Peek(10) == 0x64;
      var s12 := Lt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x05a3);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s15, gas - 1)
      else
        ExecuteFromCFGNode_s144(s15, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 72
    * Starting at 0x57f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x41);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0599);
      assert s11.Peek(0) == 0x599;
      assert s11.Peek(9) == 0x219;
      assert s11.Peek(10) == 0x64;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s12, gas - 1)
      else
        ExecuteFromCFGNode_s145(s12, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 73
    * Starting at 0x591
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x591 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x30);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Dup2(s1);
      var s3 := Sub(s2);
      var s4 := Push2(s3, 0x059e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s5, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 75
    * Starting at 0x59e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Push2(s1, 0x05a8);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s3, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 77
    * Starting at 0x5a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x219

    requires s0.stack[9] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x219;
      assert s1.Peek(9) == 0x64;
      var s2 := Push1(s1, 0x10);
      var s3 := Swap1(s2);
      var s4 := Swap3(s3);
      var s5 := Mul(s4);
      var s6 := Swap1(s5);
      var s7 := Swap2(s6);
      var s8 := Add(s7);
      var s9 := Swap3(s8);
      var s10 := Swap1(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(7) == 0x219;
      assert s11.Peek(8) == 0x64;
      var s12 := Add(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Push1(s14, 0x02);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x04e2);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s18, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 74
    * Starting at 0x599
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x599 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x219;
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x37);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s146(s4, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 76
    * Starting at 0x5a3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x219;
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x57);
      var s3 := Dup2(s2);
      var s4 := Sub(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s147(s4, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 68
    * Starting at 0x55b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x219;
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x37);
      var s3 := Dup3(s2);
      var s4 := Sub(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s142(s4, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 70
    * Starting at 0x565
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x565 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x219

    requires s0.stack[8] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x219;
      assert s1.Peek(8) == 0x64;
      var s2 := Push1(s1, 0x57);
      var s3 := Dup3(s2);
      var s4 := Sub(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s143(s4, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 78
    * Starting at 0x5be
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x219

    requires s0.stack[6] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x219;
      assert s1.Peek(6) == 0x64;
      var s2 := Pop(s1);
      var s3 := Swap4(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s8, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 30
    * Starting at 0x219
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x219 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push2(s7, 0x08fc);
      var s9 := SelfBalance(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x64;
      var s12 := IsZero(s11);
      var s13 := Mul(s12);
      var s14 := Swap1(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup1(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(8) == 0x64;
      var s22 := Sub(s21);
      var s23 := Dup2(s22);
      var s24 := Dup6(s23);
      var s25 := Dup9(s24);
      var s26 := Dup9(s25);
      var s27 := Call(s26);
      var s28 := Swap4(s27);
      var s29 := Pop(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(2) == 0x64;
      var s32 := Pop(s31);
      var s33 := IsZero(s32);
      var s34 := Dup1(s33);
      var s35 := IsZero(s34);
      var s36 := Push2(s35, 0x01ac);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s37, gas - 1)
      else
        ExecuteFromCFGNode_s154(s37, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 31
    * Starting at 0x248
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x248 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 155
    * Segment Id for this node is: 13
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
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
      var s5 := Push2(s4, 0x0072);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s6, gas - 1)
      else
        ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 14
    * Starting at 0x6e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e as nat
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

  /** Node 157
    * Segment Id for this node is: 15
    * Starting at 0x72
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x007b);
      var s4 := Push2(s3, 0x01af);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s5, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 27
    * Starting at 0x1af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x7b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x7b;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s11, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 16
    * Starting at 0x7b
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x7b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap1(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(4) == 0x7b;
      var s12 := And(s11);
      var s13 := Dup3(s12);
      var s14 := MStore(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := Swap1(s17);
      var s19 := Sub(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(2) == 0x7b;
      var s22 := Swap1(s21);
      var s23 := Return(s22);
      // Segment is terminal (Revert, Stop or Return)
      s23
  }

  /** Node 160
    * Segment Id for this node is: 9
    * Starting at 0x4f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f as nat
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
      var s5 := Push2(s4, 0x005b);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s6, gas - 1)
      else
        ExecuteFromCFGNode_s161(s6, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 10
    * Starting at 0x57
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57 as nat
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

  /** Node 162
    * Segment Id for this node is: 11
    * Starting at 0x5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0064);
      var s4 := Push2(s3, 0x00b4);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s5, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 21
    * Starting at 0xb4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x64;
      var s12 := Push2(s11, 0x0113);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s13, gas - 1)
      else
        ExecuteFromCFGNode_s164(s13, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 22
    * Starting at 0xc7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x64;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push3(s3, 0x461bcd);
      var s5 := Push1(s4, 0xe5);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x1b);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f6e6c79206f776e65722063616e2073746f702074686520626f740000000000);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(5) == 0x64;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Swap1(s23);
      var s25 := MLoad(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Swap1(s27);
      var s29 := Sub(s28);
      var s30 := Push1(s29, 0x64);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x64;
      var s32 := Swap1(s31);
      var s33 := Revert(s32);
      // Segment is terminal (Revert, Stop or Return)
      s33
  }

  /** Node 165
    * Segment Id for this node is: 23
    * Starting at 0x113
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x113 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x64;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Dup3(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x1c);
      var s10 := Swap1(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x64;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push32(s13, 0x53746f702074686520626f742066726f6d20776f726b696e672e2e2e00000000);
      var s15 := Dup2(s14);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Swap1(s18);
      var s20 := MLoad(s19);
      var s21 := Push32(s20, 0xcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab);
      assert s21.Peek(3) == 0x64;
      var s22 := Swap2(s21);
      var s23 := Dup2(s22);
      var s24 := Swap1(s23);
      var s25 := Sub(s24);
      var s26 := Push1(s25, 0x60);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Log1(s28);
      var s30 := Push1(s29, 0x01);
      var s31 := SLoad(s30);
      assert s31.Peek(1) == 0x64;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Push1(s33, 0x01);
      var s35 := Push1(s34, 0x01);
      var s36 := Push1(s35, 0xa0);
      var s37 := Shl(s36);
      var s38 := Sub(s37);
      var s39 := Swap1(s38);
      var s40 := Swap2(s39);
      var s41 := And(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s166(s41, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 24
    * Starting at 0x185
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x185 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := SelfBalance(s1);
      var s3 := Dup1(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x08fc);
      var s6 := Mul(s5);
      var s7 := Swap2(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Dup2(s8);
      var s10 := Dup2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x64;
      var s12 := Dup6(s11);
      var s13 := Dup9(s12);
      var s14 := Dup9(s13);
      var s15 := Call(s14);
      var s16 := Swap4(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(1) == 0x64;
      var s22 := Dup1(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x01ac);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s25, gas - 1)
      else
        ExecuteFromCFGNode_s167(s25, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 25
    * Starting at 0x1a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x64

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(2) == 0x64;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 168
    * Segment Id for this node is: 6
    * Starting at 0x43
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x004a);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s4, gas - 1)
      else
        ExecuteFromCFGNode_s169(s4, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 7
    * Starting at 0x49
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49 as nat
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

  /** Node 170
    * Segment Id for this node is: 8
    * Starting at 0x4a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
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
