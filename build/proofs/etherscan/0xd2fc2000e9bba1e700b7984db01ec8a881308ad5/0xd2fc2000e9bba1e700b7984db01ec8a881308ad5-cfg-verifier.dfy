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
      var s6 := Push2(s5, 0x0086);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s7, gas - 1)
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
      var s6 := Push4(s5, 0x698ed5a3);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0059);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s9, gas - 1)
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
      var s2 := Push4(s1, 0x698ed5a3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0102);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8d2677d0);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0120);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa40dabba);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x013e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s5, gas - 1)
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
      var s2 := Push4(s1, 0xe19419be);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x015c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x55
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x0086);
      assert s1.Peek(0) == 0x86;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s2, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86 as nat
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

  /** Node 10
    * Segment Id for this node is: 35
    * Starting at 0x15c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0164);
      var s3 := Push2(s2, 0x027b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s4, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 45
    * Starting at 0x27b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x164;
      var s2 := Push1(s1, 0x06);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x164;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s14, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 36
    * Starting at 0x164
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x164 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x164;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0171);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x031a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s8, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 58
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x171

    requires s0.stack[3] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x171;
      assert s1.Peek(3) == 0x164;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x032d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x32d;
      assert s11.Peek(5) == 0x171;
      assert s11.Peek(6) == 0x164;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x030b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s14, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 56
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x32d

    requires s0.stack[6] == 0x171

    requires s0.stack[7] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(6) == 0x171;
      assert s1.Peek(7) == 0x164;
      var s2 := Push2(s1, 0x0314);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s5, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 54
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x314

    requires s0.stack[4] == 0x32d

    requires s0.stack[8] == 0x171

    requires s0.stack[9] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(4) == 0x32d;
      assert s1.Peek(8) == 0x171;
      assert s1.Peek(9) == 0x164;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0304);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s6, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x304

    requires s0.stack[4] == 0x314

    requires s0.stack[7] == 0x32d

    requires s0.stack[11] == 0x171

    requires s0.stack[12] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x304;
      assert s1.Peek(4) == 0x314;
      assert s1.Peek(7) == 0x32d;
      assert s1.Peek(11) == 0x171;
      assert s1.Peek(12) == 0x164;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s6, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x304

    requires s0.stack[7] == 0x314

    requires s0.stack[10] == 0x32d

    requires s0.stack[14] == 0x171

    requires s0.stack[15] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(7) == 0x314;
      assert s1.Peek(10) == 0x32d;
      assert s1.Peek(14) == 0x171;
      assert s1.Peek(15) == 0x164;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s8, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x304

    requires s0.stack[12] == 0x314

    requires s0.stack[15] == 0x32d

    requires s0.stack[19] == 0x171

    requires s0.stack[20] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x304;
      assert s1.Peek(12) == 0x314;
      assert s1.Peek(15) == 0x32d;
      assert s1.Peek(19) == 0x171;
      assert s1.Peek(20) == 0x164;
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
      ExecuteFromCFGNode_s19(s11, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x171

    requires s0.stack[19] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x171;
      assert s1.Peek(19) == 0x164;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s3, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x171

    requires s0.stack[19] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x171;
      assert s1.Peek(19) == 0x164;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s9, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x171

    requires s0.stack[18] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x171;
      assert s1.Peek(18) == 0x164;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x171

    requires s0.stack[18] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x171;
      assert s1.Peek(18) == 0x164;
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
      ExecuteFromCFGNode_s23(s11, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x304

    requires s0.stack[9] == 0x314

    requires s0.stack[12] == 0x32d

    requires s0.stack[16] == 0x171

    requires s0.stack[17] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x304;
      assert s1.Peek(9) == 0x314;
      assert s1.Peek(12) == 0x32d;
      assert s1.Peek(16) == 0x171;
      assert s1.Peek(17) == 0x164;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s7, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x304

    requires s0.stack[6] == 0x314

    requires s0.stack[9] == 0x32d

    requires s0.stack[13] == 0x171

    requires s0.stack[14] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(6) == 0x314;
      assert s1.Peek(9) == 0x32d;
      assert s1.Peek(13) == 0x171;
      assert s1.Peek(14) == 0x164;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s7, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x314

    requires s0.stack[6] == 0x32d

    requires s0.stack[10] == 0x171

    requires s0.stack[11] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x314;
      assert s1.Peek(6) == 0x32d;
      assert s1.Peek(10) == 0x171;
      assert s1.Peek(11) == 0x164;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s7, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 57
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x32d

    requires s0.stack[7] == 0x171

    requires s0.stack[8] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(7) == 0x171;
      assert s1.Peek(8) == 0x164;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s6, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 59
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x171

    requires s0.stack[4] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x171;
      assert s1.Peek(4) == 0x164;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s6, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 37
    * Starting at 0x171
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x171 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x164

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x164;
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

  /** Node 29
    * Segment Id for this node is: 32
    * Starting at 0x13e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0146);
      var s3 := Push2(s2, 0x0256);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s4, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 44
    * Starting at 0x256
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x146;
      var s2 := Push1(s1, 0x01);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x146;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s14, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 33
    * Starting at 0x146
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x146;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0153);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x031a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s8, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 58
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x153

    requires s0.stack[3] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x153;
      assert s1.Peek(3) == 0x146;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x032d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x32d;
      assert s11.Peek(5) == 0x153;
      assert s11.Peek(6) == 0x146;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x030b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s14, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 56
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x32d

    requires s0.stack[6] == 0x153

    requires s0.stack[7] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(6) == 0x153;
      assert s1.Peek(7) == 0x146;
      var s2 := Push2(s1, 0x0314);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 54
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x314

    requires s0.stack[4] == 0x32d

    requires s0.stack[8] == 0x153

    requires s0.stack[9] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(4) == 0x32d;
      assert s1.Peek(8) == 0x153;
      assert s1.Peek(9) == 0x146;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0304);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s6, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x304

    requires s0.stack[4] == 0x314

    requires s0.stack[7] == 0x32d

    requires s0.stack[11] == 0x153

    requires s0.stack[12] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x304;
      assert s1.Peek(4) == 0x314;
      assert s1.Peek(7) == 0x32d;
      assert s1.Peek(11) == 0x153;
      assert s1.Peek(12) == 0x146;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s6, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x304

    requires s0.stack[7] == 0x314

    requires s0.stack[10] == 0x32d

    requires s0.stack[14] == 0x153

    requires s0.stack[15] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(7) == 0x314;
      assert s1.Peek(10) == 0x32d;
      assert s1.Peek(14) == 0x153;
      assert s1.Peek(15) == 0x146;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s8, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x304

    requires s0.stack[12] == 0x314

    requires s0.stack[15] == 0x32d

    requires s0.stack[19] == 0x153

    requires s0.stack[20] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x304;
      assert s1.Peek(12) == 0x314;
      assert s1.Peek(15) == 0x32d;
      assert s1.Peek(19) == 0x153;
      assert s1.Peek(20) == 0x146;
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
      ExecuteFromCFGNode_s38(s11, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x153

    requires s0.stack[19] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x153;
      assert s1.Peek(19) == 0x146;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s3, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x153

    requires s0.stack[19] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x153;
      assert s1.Peek(19) == 0x146;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s9, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x153

    requires s0.stack[18] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x153;
      assert s1.Peek(18) == 0x146;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s3, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x153

    requires s0.stack[18] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x153;
      assert s1.Peek(18) == 0x146;
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
      ExecuteFromCFGNode_s42(s11, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x304

    requires s0.stack[9] == 0x314

    requires s0.stack[12] == 0x32d

    requires s0.stack[16] == 0x153

    requires s0.stack[17] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x304;
      assert s1.Peek(9) == 0x314;
      assert s1.Peek(12) == 0x32d;
      assert s1.Peek(16) == 0x153;
      assert s1.Peek(17) == 0x146;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s7, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x304

    requires s0.stack[6] == 0x314

    requires s0.stack[9] == 0x32d

    requires s0.stack[13] == 0x153

    requires s0.stack[14] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(6) == 0x314;
      assert s1.Peek(9) == 0x32d;
      assert s1.Peek(13) == 0x153;
      assert s1.Peek(14) == 0x146;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x314

    requires s0.stack[6] == 0x32d

    requires s0.stack[10] == 0x153

    requires s0.stack[11] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x314;
      assert s1.Peek(6) == 0x32d;
      assert s1.Peek(10) == 0x153;
      assert s1.Peek(11) == 0x146;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s7, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 57
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x32d

    requires s0.stack[7] == 0x153

    requires s0.stack[8] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(7) == 0x153;
      assert s1.Peek(8) == 0x146;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s6, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 59
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x153

    requires s0.stack[4] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x153;
      assert s1.Peek(4) == 0x146;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s6, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 34
    * Starting at 0x153
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x146

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x146;
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
    * Segment Id for this node is: 29
    * Starting at 0x120
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0128);
      var s3 := Push2(s2, 0x0231);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s4, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 43
    * Starting at 0x231
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x231 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x128;
      var s2 := Push1(s1, 0x07);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x128;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s14, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 30
    * Starting at 0x128
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x128 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0135);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x038c);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s8, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 70
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x135

    requires s0.stack[3] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x135;
      assert s1.Peek(3) == 0x128;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x039f);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x39f;
      assert s11.Peek(5) == 0x135;
      assert s11.Peek(6) == 0x128;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x037d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s14, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 68
    * Starting at 0x37d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x39f

    requires s0.stack[6] == 0x135

    requires s0.stack[7] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x39f;
      assert s1.Peek(6) == 0x135;
      assert s1.Peek(7) == 0x128;
      var s2 := Push2(s1, 0x0386);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x036c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s5, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 66
    * Starting at 0x36c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x386

    requires s0.stack[4] == 0x39f

    requires s0.stack[8] == 0x135

    requires s0.stack[9] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x386;
      assert s1.Peek(4) == 0x39f;
      assert s1.Peek(8) == 0x135;
      assert s1.Peek(9) == 0x128;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0376);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x376

    requires s0.stack[4] == 0x386

    requires s0.stack[7] == 0x39f

    requires s0.stack[11] == 0x135

    requires s0.stack[12] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x376;
      assert s1.Peek(4) == 0x386;
      assert s1.Peek(7) == 0x39f;
      assert s1.Peek(11) == 0x135;
      assert s1.Peek(12) == 0x128;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x376

    requires s0.stack[7] == 0x386

    requires s0.stack[10] == 0x39f

    requires s0.stack[14] == 0x135

    requires s0.stack[15] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x376;
      assert s1.Peek(7) == 0x386;
      assert s1.Peek(10) == 0x39f;
      assert s1.Peek(14) == 0x135;
      assert s1.Peek(15) == 0x128;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s8, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x376

    requires s0.stack[12] == 0x386

    requires s0.stack[15] == 0x39f

    requires s0.stack[19] == 0x135

    requires s0.stack[20] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x376;
      assert s1.Peek(12) == 0x386;
      assert s1.Peek(15) == 0x39f;
      assert s1.Peek(19) == 0x135;
      assert s1.Peek(20) == 0x128;
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
      ExecuteFromCFGNode_s57(s11, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x376

    requires s0.stack[11] == 0x386

    requires s0.stack[14] == 0x39f

    requires s0.stack[18] == 0x135

    requires s0.stack[19] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x376;
      assert s1.Peek(11) == 0x386;
      assert s1.Peek(14) == 0x39f;
      assert s1.Peek(18) == 0x135;
      assert s1.Peek(19) == 0x128;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s3, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x376

    requires s0.stack[11] == 0x386

    requires s0.stack[14] == 0x39f

    requires s0.stack[18] == 0x135

    requires s0.stack[19] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x376;
      assert s1.Peek(11) == 0x386;
      assert s1.Peek(14) == 0x39f;
      assert s1.Peek(18) == 0x135;
      assert s1.Peek(19) == 0x128;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s9, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x376

    requires s0.stack[10] == 0x386

    requires s0.stack[13] == 0x39f

    requires s0.stack[17] == 0x135

    requires s0.stack[18] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x376;
      assert s1.Peek(10) == 0x386;
      assert s1.Peek(13) == 0x39f;
      assert s1.Peek(17) == 0x135;
      assert s1.Peek(18) == 0x128;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s3, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x376

    requires s0.stack[10] == 0x386

    requires s0.stack[13] == 0x39f

    requires s0.stack[17] == 0x135

    requires s0.stack[18] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x376;
      assert s1.Peek(10) == 0x386;
      assert s1.Peek(13) == 0x39f;
      assert s1.Peek(17) == 0x135;
      assert s1.Peek(18) == 0x128;
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
      ExecuteFromCFGNode_s61(s11, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x376

    requires s0.stack[9] == 0x386

    requires s0.stack[12] == 0x39f

    requires s0.stack[16] == 0x135

    requires s0.stack[17] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x376;
      assert s1.Peek(9) == 0x386;
      assert s1.Peek(12) == 0x39f;
      assert s1.Peek(16) == 0x135;
      assert s1.Peek(17) == 0x128;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s7, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x376

    requires s0.stack[6] == 0x386

    requires s0.stack[9] == 0x39f

    requires s0.stack[13] == 0x135

    requires s0.stack[14] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x376;
      assert s1.Peek(6) == 0x386;
      assert s1.Peek(9) == 0x39f;
      assert s1.Peek(13) == 0x135;
      assert s1.Peek(14) == 0x128;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s7, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 67
    * Starting at 0x376
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x376 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x386

    requires s0.stack[6] == 0x39f

    requires s0.stack[10] == 0x135

    requires s0.stack[11] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x386;
      assert s1.Peek(6) == 0x39f;
      assert s1.Peek(10) == 0x135;
      assert s1.Peek(11) == 0x128;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s7, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 69
    * Starting at 0x386
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x386 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x39f

    requires s0.stack[7] == 0x135

    requires s0.stack[8] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x39f;
      assert s1.Peek(7) == 0x135;
      assert s1.Peek(8) == 0x128;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s6, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 71
    * Starting at 0x39f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x135

    requires s0.stack[4] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x135;
      assert s1.Peek(4) == 0x128;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 31
    * Starting at 0x135
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x135 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x128

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x128;
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

  /** Node 67
    * Segment Id for this node is: 26
    * Starting at 0x102
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x010a);
      var s3 := Push2(s2, 0x020c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s4, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 42
    * Starting at 0x20c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x10a;
      var s2 := Push1(s1, 0x02);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x10a;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s14, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 27
    * Starting at 0x10a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10a;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0117);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x031a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s8, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 58
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x117

    requires s0.stack[3] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x117;
      assert s1.Peek(3) == 0x10a;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x032d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x32d;
      assert s11.Peek(5) == 0x117;
      assert s11.Peek(6) == 0x10a;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x030b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s14, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 56
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x32d

    requires s0.stack[6] == 0x117

    requires s0.stack[7] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(6) == 0x117;
      assert s1.Peek(7) == 0x10a;
      var s2 := Push2(s1, 0x0314);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s5, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 54
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x314

    requires s0.stack[4] == 0x32d

    requires s0.stack[8] == 0x117

    requires s0.stack[9] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(4) == 0x32d;
      assert s1.Peek(8) == 0x117;
      assert s1.Peek(9) == 0x10a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0304);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s6, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x304

    requires s0.stack[4] == 0x314

    requires s0.stack[7] == 0x32d

    requires s0.stack[11] == 0x117

    requires s0.stack[12] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x304;
      assert s1.Peek(4) == 0x314;
      assert s1.Peek(7) == 0x32d;
      assert s1.Peek(11) == 0x117;
      assert s1.Peek(12) == 0x10a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s6, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x304

    requires s0.stack[7] == 0x314

    requires s0.stack[10] == 0x32d

    requires s0.stack[14] == 0x117

    requires s0.stack[15] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(7) == 0x314;
      assert s1.Peek(10) == 0x32d;
      assert s1.Peek(14) == 0x117;
      assert s1.Peek(15) == 0x10a;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s8, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x304

    requires s0.stack[12] == 0x314

    requires s0.stack[15] == 0x32d

    requires s0.stack[19] == 0x117

    requires s0.stack[20] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x304;
      assert s1.Peek(12) == 0x314;
      assert s1.Peek(15) == 0x32d;
      assert s1.Peek(19) == 0x117;
      assert s1.Peek(20) == 0x10a;
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
      ExecuteFromCFGNode_s76(s11, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x117

    requires s0.stack[19] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x117;
      assert s1.Peek(19) == 0x10a;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s3, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x117

    requires s0.stack[19] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x117;
      assert s1.Peek(19) == 0x10a;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s9, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x117

    requires s0.stack[18] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x117;
      assert s1.Peek(18) == 0x10a;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s3, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x117

    requires s0.stack[18] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x117;
      assert s1.Peek(18) == 0x10a;
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
      ExecuteFromCFGNode_s80(s11, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x304

    requires s0.stack[9] == 0x314

    requires s0.stack[12] == 0x32d

    requires s0.stack[16] == 0x117

    requires s0.stack[17] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x304;
      assert s1.Peek(9) == 0x314;
      assert s1.Peek(12) == 0x32d;
      assert s1.Peek(16) == 0x117;
      assert s1.Peek(17) == 0x10a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s7, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x304

    requires s0.stack[6] == 0x314

    requires s0.stack[9] == 0x32d

    requires s0.stack[13] == 0x117

    requires s0.stack[14] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(6) == 0x314;
      assert s1.Peek(9) == 0x32d;
      assert s1.Peek(13) == 0x117;
      assert s1.Peek(14) == 0x10a;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s7, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x314

    requires s0.stack[6] == 0x32d

    requires s0.stack[10] == 0x117

    requires s0.stack[11] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x314;
      assert s1.Peek(6) == 0x32d;
      assert s1.Peek(10) == 0x117;
      assert s1.Peek(11) == 0x10a;
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
    * Segment Id for this node is: 57
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x32d

    requires s0.stack[7] == 0x117

    requires s0.stack[8] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(7) == 0x117;
      assert s1.Peek(8) == 0x10a;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s6, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 59
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x117

    requires s0.stack[4] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x117;
      assert s1.Peek(4) == 0x10a;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 28
    * Starting at 0x117
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x117 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x10a

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x10a;
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

  /** Node 86
    * Segment Id for this node is: 9
    * Starting at 0x59
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x12d05fd7);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x008a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s147(s6, gas - 1)
      else
        ExecuteFromCFGNode_s87(s6, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 10
    * Starting at 0x65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1ae8c36e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00a8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s5, gas - 1)
      else
        ExecuteFromCFGNode_s88(s5, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 11
    * Starting at 0x70
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1c5573dc);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00c6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s5, gas - 1)
      else
        ExecuteFromCFGNode_s89(s5, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 12
    * Starting at 0x7b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x30f108e8);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00e4);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 23
    * Starting at 0xe4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ec);
      var s3 := Push2(s2, 0x01e7);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s4, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 41
    * Starting at 0x1e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xec;
      var s2 := Push1(s1, 0x03);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0xec;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s14, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 24
    * Starting at 0xec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00f9);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x031a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s8, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 58
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xf9

    requires s0.stack[3] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf9;
      assert s1.Peek(3) == 0xec;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x032d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x32d;
      assert s11.Peek(5) == 0xf9;
      assert s11.Peek(6) == 0xec;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x030b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s14, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 56
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x32d

    requires s0.stack[6] == 0xf9

    requires s0.stack[7] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(6) == 0xf9;
      assert s1.Peek(7) == 0xec;
      var s2 := Push2(s1, 0x0314);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s5, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 54
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x314

    requires s0.stack[4] == 0x32d

    requires s0.stack[8] == 0xf9

    requires s0.stack[9] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(4) == 0x32d;
      assert s1.Peek(8) == 0xf9;
      assert s1.Peek(9) == 0xec;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0304);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s6, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x304

    requires s0.stack[4] == 0x314

    requires s0.stack[7] == 0x32d

    requires s0.stack[11] == 0xf9

    requires s0.stack[12] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x304;
      assert s1.Peek(4) == 0x314;
      assert s1.Peek(7) == 0x32d;
      assert s1.Peek(11) == 0xf9;
      assert s1.Peek(12) == 0xec;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s6, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x304

    requires s0.stack[7] == 0x314

    requires s0.stack[10] == 0x32d

    requires s0.stack[14] == 0xf9

    requires s0.stack[15] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(7) == 0x314;
      assert s1.Peek(10) == 0x32d;
      assert s1.Peek(14) == 0xf9;
      assert s1.Peek(15) == 0xec;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s8, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x304

    requires s0.stack[12] == 0x314

    requires s0.stack[15] == 0x32d

    requires s0.stack[19] == 0xf9

    requires s0.stack[20] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x304;
      assert s1.Peek(12) == 0x314;
      assert s1.Peek(15) == 0x32d;
      assert s1.Peek(19) == 0xf9;
      assert s1.Peek(20) == 0xec;
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
      ExecuteFromCFGNode_s99(s11, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0xf9

    requires s0.stack[19] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0xf9;
      assert s1.Peek(19) == 0xec;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s3, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0xf9

    requires s0.stack[19] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0xf9;
      assert s1.Peek(19) == 0xec;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s9, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0xf9

    requires s0.stack[18] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0xf9;
      assert s1.Peek(18) == 0xec;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s3, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0xf9

    requires s0.stack[18] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0xf9;
      assert s1.Peek(18) == 0xec;
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
      ExecuteFromCFGNode_s103(s11, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x304

    requires s0.stack[9] == 0x314

    requires s0.stack[12] == 0x32d

    requires s0.stack[16] == 0xf9

    requires s0.stack[17] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x304;
      assert s1.Peek(9) == 0x314;
      assert s1.Peek(12) == 0x32d;
      assert s1.Peek(16) == 0xf9;
      assert s1.Peek(17) == 0xec;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s7, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x304

    requires s0.stack[6] == 0x314

    requires s0.stack[9] == 0x32d

    requires s0.stack[13] == 0xf9

    requires s0.stack[14] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(6) == 0x314;
      assert s1.Peek(9) == 0x32d;
      assert s1.Peek(13) == 0xf9;
      assert s1.Peek(14) == 0xec;
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
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x314

    requires s0.stack[6] == 0x32d

    requires s0.stack[10] == 0xf9

    requires s0.stack[11] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x314;
      assert s1.Peek(6) == 0x32d;
      assert s1.Peek(10) == 0xf9;
      assert s1.Peek(11) == 0xec;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s7, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 57
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x32d

    requires s0.stack[7] == 0xf9

    requires s0.stack[8] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(7) == 0xf9;
      assert s1.Peek(8) == 0xec;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s6, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 59
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xf9

    requires s0.stack[4] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf9;
      assert s1.Peek(4) == 0xec;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s6, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 25
    * Starting at 0xf9
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xec

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xec;
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

  /** Node 109
    * Segment Id for this node is: 20
    * Starting at 0xc6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00ce);
      var s3 := Push2(s2, 0x01c4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s4, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 40
    * Starting at 0x1c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xce;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Swap1(s7);
      var s9 := Div(s8);
      var s10 := Push20(s9, 0xffffffffffffffffffffffffffffffffffffffff);
      var s11 := And(s10);
      assert s11.Peek(1) == 0xce;
      var s12 := Dup2(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s13, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 21
    * Starting at 0xce
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xce;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00db);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0353);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s8, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 64
    * Starting at 0x353
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x353 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xdb

    requires s0.stack[3] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xdb;
      assert s1.Peek(3) == 0xce;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0366);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x366;
      assert s11.Peek(5) == 0xdb;
      assert s11.Peek(6) == 0xce;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x0344);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 62
    * Starting at 0x344
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x366

    requires s0.stack[6] == 0xdb

    requires s0.stack[7] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x366;
      assert s1.Peek(6) == 0xdb;
      assert s1.Peek(7) == 0xce;
      var s2 := Push2(s1, 0x034d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0333);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s5, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 60
    * Starting at 0x333
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x333 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x34d

    requires s0.stack[4] == 0x366

    requires s0.stack[8] == 0xdb

    requires s0.stack[9] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x34d;
      assert s1.Peek(4) == 0x366;
      assert s1.Peek(8) == 0xdb;
      assert s1.Peek(9) == 0xce;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x033d);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s6, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x33d

    requires s0.stack[4] == 0x34d

    requires s0.stack[7] == 0x366

    requires s0.stack[11] == 0xdb

    requires s0.stack[12] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x33d;
      assert s1.Peek(4) == 0x34d;
      assert s1.Peek(7) == 0x366;
      assert s1.Peek(11) == 0xdb;
      assert s1.Peek(12) == 0xce;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s6, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x33d

    requires s0.stack[7] == 0x34d

    requires s0.stack[10] == 0x366

    requires s0.stack[14] == 0xdb

    requires s0.stack[15] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x33d;
      assert s1.Peek(7) == 0x34d;
      assert s1.Peek(10) == 0x366;
      assert s1.Peek(14) == 0xdb;
      assert s1.Peek(15) == 0xce;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s8, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x33d

    requires s0.stack[12] == 0x34d

    requires s0.stack[15] == 0x366

    requires s0.stack[19] == 0xdb

    requires s0.stack[20] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x33d;
      assert s1.Peek(12) == 0x34d;
      assert s1.Peek(15) == 0x366;
      assert s1.Peek(19) == 0xdb;
      assert s1.Peek(20) == 0xce;
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
      ExecuteFromCFGNode_s118(s11, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x33d

    requires s0.stack[11] == 0x34d

    requires s0.stack[14] == 0x366

    requires s0.stack[18] == 0xdb

    requires s0.stack[19] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(11) == 0x34d;
      assert s1.Peek(14) == 0x366;
      assert s1.Peek(18) == 0xdb;
      assert s1.Peek(19) == 0xce;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s3, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x33d

    requires s0.stack[11] == 0x34d

    requires s0.stack[14] == 0x366

    requires s0.stack[18] == 0xdb

    requires s0.stack[19] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x33d;
      assert s1.Peek(11) == 0x34d;
      assert s1.Peek(14) == 0x366;
      assert s1.Peek(18) == 0xdb;
      assert s1.Peek(19) == 0xce;
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
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x33d

    requires s0.stack[10] == 0x34d

    requires s0.stack[13] == 0x366

    requires s0.stack[17] == 0xdb

    requires s0.stack[18] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x33d;
      assert s1.Peek(10) == 0x34d;
      assert s1.Peek(13) == 0x366;
      assert s1.Peek(17) == 0xdb;
      assert s1.Peek(18) == 0xce;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s3, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x33d

    requires s0.stack[10] == 0x34d

    requires s0.stack[13] == 0x366

    requires s0.stack[17] == 0xdb

    requires s0.stack[18] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x33d;
      assert s1.Peek(10) == 0x34d;
      assert s1.Peek(13) == 0x366;
      assert s1.Peek(17) == 0xdb;
      assert s1.Peek(18) == 0xce;
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
      ExecuteFromCFGNode_s122(s11, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x33d

    requires s0.stack[9] == 0x34d

    requires s0.stack[12] == 0x366

    requires s0.stack[16] == 0xdb

    requires s0.stack[17] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x33d;
      assert s1.Peek(9) == 0x34d;
      assert s1.Peek(12) == 0x366;
      assert s1.Peek(16) == 0xdb;
      assert s1.Peek(17) == 0xce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s7, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x33d

    requires s0.stack[6] == 0x34d

    requires s0.stack[9] == 0x366

    requires s0.stack[13] == 0xdb

    requires s0.stack[14] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x33d;
      assert s1.Peek(6) == 0x34d;
      assert s1.Peek(9) == 0x366;
      assert s1.Peek(13) == 0xdb;
      assert s1.Peek(14) == 0xce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s7, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 61
    * Starting at 0x33d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x34d

    requires s0.stack[6] == 0x366

    requires s0.stack[10] == 0xdb

    requires s0.stack[11] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x34d;
      assert s1.Peek(6) == 0x366;
      assert s1.Peek(10) == 0xdb;
      assert s1.Peek(11) == 0xce;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s7, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 63
    * Starting at 0x34d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x366

    requires s0.stack[7] == 0xdb

    requires s0.stack[8] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x366;
      assert s1.Peek(7) == 0xdb;
      assert s1.Peek(8) == 0xce;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s6, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 65
    * Starting at 0x366
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x366 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xdb

    requires s0.stack[4] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdb;
      assert s1.Peek(4) == 0xce;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s6, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 22
    * Starting at 0xdb
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xce

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xce;
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

  /** Node 128
    * Segment Id for this node is: 17
    * Starting at 0xa8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b0);
      var s3 := Push2(s2, 0x019f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s4, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 39
    * Starting at 0x19f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb0;
      var s2 := Push1(s1, 0x05);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0xb0;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s14, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 18
    * Starting at 0xb0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb0;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x00bd);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x031a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s8, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 58
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xbd

    requires s0.stack[3] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbd;
      assert s1.Peek(3) == 0xb0;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x032d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x32d;
      assert s11.Peek(5) == 0xbd;
      assert s11.Peek(6) == 0xb0;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x030b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s14, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 56
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x32d

    requires s0.stack[6] == 0xbd

    requires s0.stack[7] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(6) == 0xbd;
      assert s1.Peek(7) == 0xb0;
      var s2 := Push2(s1, 0x0314);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s5, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 54
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x314

    requires s0.stack[4] == 0x32d

    requires s0.stack[8] == 0xbd

    requires s0.stack[9] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(4) == 0x32d;
      assert s1.Peek(8) == 0xbd;
      assert s1.Peek(9) == 0xb0;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0304);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s6, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x304

    requires s0.stack[4] == 0x314

    requires s0.stack[7] == 0x32d

    requires s0.stack[11] == 0xbd

    requires s0.stack[12] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x304;
      assert s1.Peek(4) == 0x314;
      assert s1.Peek(7) == 0x32d;
      assert s1.Peek(11) == 0xbd;
      assert s1.Peek(12) == 0xb0;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s6, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x304

    requires s0.stack[7] == 0x314

    requires s0.stack[10] == 0x32d

    requires s0.stack[14] == 0xbd

    requires s0.stack[15] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(7) == 0x314;
      assert s1.Peek(10) == 0x32d;
      assert s1.Peek(14) == 0xbd;
      assert s1.Peek(15) == 0xb0;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s8, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x304

    requires s0.stack[12] == 0x314

    requires s0.stack[15] == 0x32d

    requires s0.stack[19] == 0xbd

    requires s0.stack[20] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x304;
      assert s1.Peek(12) == 0x314;
      assert s1.Peek(15) == 0x32d;
      assert s1.Peek(19) == 0xbd;
      assert s1.Peek(20) == 0xb0;
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
      ExecuteFromCFGNode_s137(s11, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0xbd

    requires s0.stack[19] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0xbd;
      assert s1.Peek(19) == 0xb0;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s3, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0xbd

    requires s0.stack[19] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0xbd;
      assert s1.Peek(19) == 0xb0;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s9, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0xbd

    requires s0.stack[18] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0xbd;
      assert s1.Peek(18) == 0xb0;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s3, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0xbd

    requires s0.stack[18] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0xbd;
      assert s1.Peek(18) == 0xb0;
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
      ExecuteFromCFGNode_s141(s11, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x304

    requires s0.stack[9] == 0x314

    requires s0.stack[12] == 0x32d

    requires s0.stack[16] == 0xbd

    requires s0.stack[17] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x304;
      assert s1.Peek(9) == 0x314;
      assert s1.Peek(12) == 0x32d;
      assert s1.Peek(16) == 0xbd;
      assert s1.Peek(17) == 0xb0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s7, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x304

    requires s0.stack[6] == 0x314

    requires s0.stack[9] == 0x32d

    requires s0.stack[13] == 0xbd

    requires s0.stack[14] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(6) == 0x314;
      assert s1.Peek(9) == 0x32d;
      assert s1.Peek(13) == 0xbd;
      assert s1.Peek(14) == 0xb0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s7, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x314

    requires s0.stack[6] == 0x32d

    requires s0.stack[10] == 0xbd

    requires s0.stack[11] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x314;
      assert s1.Peek(6) == 0x32d;
      assert s1.Peek(10) == 0xbd;
      assert s1.Peek(11) == 0xb0;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s7, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 57
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x32d

    requires s0.stack[7] == 0xbd

    requires s0.stack[8] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(7) == 0xbd;
      assert s1.Peek(8) == 0xb0;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s6, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 59
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xbd

    requires s0.stack[4] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbd;
      assert s1.Peek(4) == 0xb0;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s6, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 19
    * Starting at 0xbd
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb0;
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

  /** Node 147
    * Segment Id for this node is: 14
    * Starting at 0x8a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0092);
      var s3 := Push2(s2, 0x017a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s4, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 38
    * Starting at 0x17a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x92;
      var s2 := Push1(s1, 0x04);
      var s3 := Push0(s2);
      var s4 := Swap1(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0100);
      var s8 := Exp(s7);
      var s9 := Swap1(s8);
      var s10 := Div(s9);
      var s11 := Push20(s10, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s11.Peek(2) == 0x92;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s14, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 15
    * Starting at 0x92
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x92;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x009f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x031a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s8, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 58
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x9f

    requires s0.stack[3] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9f;
      assert s1.Peek(3) == 0x92;
      var s2 := Push0(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x032d);
      var s9 := Push0(s8);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x32d;
      assert s11.Peek(5) == 0x9f;
      assert s11.Peek(6) == 0x92;
      var s12 := Dup5(s11);
      var s13 := Push2(s12, 0x030b);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s14, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 56
    * Starting at 0x30b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x32d

    requires s0.stack[6] == 0x9f

    requires s0.stack[7] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32d;
      assert s1.Peek(6) == 0x9f;
      assert s1.Peek(7) == 0x92;
      var s2 := Push2(s1, 0x0314);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x02fa);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s5, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 54
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x314

    requires s0.stack[4] == 0x32d

    requires s0.stack[8] == 0x9f

    requires s0.stack[9] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x314;
      assert s1.Peek(4) == 0x32d;
      assert s1.Peek(8) == 0x9f;
      assert s1.Peek(9) == 0x92;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x0304);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02e9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s6, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 52
    * Starting at 0x2e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x304

    requires s0.stack[4] == 0x314

    requires s0.stack[7] == 0x32d

    requires s0.stack[11] == 0x9f

    requires s0.stack[12] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x304;
      assert s1.Peek(4) == 0x314;
      assert s1.Peek(7) == 0x32d;
      assert s1.Peek(11) == 0x9f;
      assert s1.Peek(12) == 0x92;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02f3);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s6, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 48
    * Starting at 0x2c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x2f3

    requires s0.stack[4] == 0x304

    requires s0.stack[7] == 0x314

    requires s0.stack[10] == 0x32d

    requires s0.stack[14] == 0x9f

    requires s0.stack[15] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2f3;
      assert s1.Peek(4) == 0x304;
      assert s1.Peek(7) == 0x314;
      assert s1.Peek(10) == 0x32d;
      assert s1.Peek(14) == 0x9f;
      assert s1.Peek(15) == 0x92;
      var s2 := Push0(s1);
      var s3 := Push2(s2, 0x02e2);
      var s4 := Push2(s3, 0x02dd);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x02a0);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s8, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x2d8

    requires s0.stack[2] == 0x2dd

    requires s0.stack[3] == 0x2e2

    requires s0.stack[6] == 0x2f3

    requires s0.stack[9] == 0x304

    requires s0.stack[12] == 0x314

    requires s0.stack[15] == 0x32d

    requires s0.stack[19] == 0x9f

    requires s0.stack[20] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2d8;
      assert s1.Peek(2) == 0x2dd;
      assert s1.Peek(3) == 0x2e2;
      assert s1.Peek(6) == 0x2f3;
      assert s1.Peek(9) == 0x304;
      assert s1.Peek(12) == 0x314;
      assert s1.Peek(15) == 0x32d;
      assert s1.Peek(19) == 0x9f;
      assert s1.Peek(20) == 0x92;
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
      ExecuteFromCFGNode_s156(s11, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 49
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x9f

    requires s0.stack[19] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x9f;
      assert s1.Peek(19) == 0x92;
      var s2 := Push2(s1, 0x02bf);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s3, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 47
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x2dd

    requires s0.stack[2] == 0x2e2

    requires s0.stack[5] == 0x2f3

    requires s0.stack[8] == 0x304

    requires s0.stack[11] == 0x314

    requires s0.stack[14] == 0x32d

    requires s0.stack[18] == 0x9f

    requires s0.stack[19] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2dd;
      assert s1.Peek(2) == 0x2e2;
      assert s1.Peek(5) == 0x2f3;
      assert s1.Peek(8) == 0x304;
      assert s1.Peek(11) == 0x314;
      assert s1.Peek(14) == 0x32d;
      assert s1.Peek(18) == 0x9f;
      assert s1.Peek(19) == 0x92;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s9, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 50
    * Starting at 0x2dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x9f

    requires s0.stack[18] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x9f;
      assert s1.Peek(18) == 0x92;
      var s2 := Push2(s1, 0x02a0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s3, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 46
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x2e2

    requires s0.stack[4] == 0x2f3

    requires s0.stack[7] == 0x304

    requires s0.stack[10] == 0x314

    requires s0.stack[13] == 0x32d

    requires s0.stack[17] == 0x9f

    requires s0.stack[18] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2e2;
      assert s1.Peek(4) == 0x2f3;
      assert s1.Peek(7) == 0x304;
      assert s1.Peek(10) == 0x314;
      assert s1.Peek(13) == 0x32d;
      assert s1.Peek(17) == 0x9f;
      assert s1.Peek(18) == 0x92;
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
      ExecuteFromCFGNode_s160(s11, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 51
    * Starting at 0x2e2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2f3

    requires s0.stack[6] == 0x304

    requires s0.stack[9] == 0x314

    requires s0.stack[12] == 0x32d

    requires s0.stack[16] == 0x9f

    requires s0.stack[17] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f3;
      assert s1.Peek(6) == 0x304;
      assert s1.Peek(9) == 0x314;
      assert s1.Peek(12) == 0x32d;
      assert s1.Peek(16) == 0x9f;
      assert s1.Peek(17) == 0x92;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s7, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 53
    * Starting at 0x2f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x304

    requires s0.stack[6] == 0x314

    requires s0.stack[9] == 0x32d

    requires s0.stack[13] == 0x9f

    requires s0.stack[14] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x304;
      assert s1.Peek(6) == 0x314;
      assert s1.Peek(9) == 0x32d;
      assert s1.Peek(13) == 0x9f;
      assert s1.Peek(14) == 0x92;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s7, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 55
    * Starting at 0x304
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x304 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x314

    requires s0.stack[6] == 0x32d

    requires s0.stack[10] == 0x9f

    requires s0.stack[11] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x314;
      assert s1.Peek(6) == 0x32d;
      assert s1.Peek(10) == 0x9f;
      assert s1.Peek(11) == 0x92;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s7, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 57
    * Starting at 0x314
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x314 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x32d

    requires s0.stack[7] == 0x9f

    requires s0.stack[8] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x32d;
      assert s1.Peek(7) == 0x9f;
      assert s1.Peek(8) == 0x92;
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s6, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 59
    * Starting at 0x32d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x9f

    requires s0.stack[4] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9f;
      assert s1.Peek(4) == 0x92;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s6, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 16
    * Starting at 0x9f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x92

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x92;
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

  /** Node 166
    * Segment Id for this node is: 13
    * Starting at 0x86
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86 as nat
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
