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
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := CallDataSize(s5);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0012);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s2(s10, gas - 1)
      else
        ExecuteFromCFGNode_s1(s10, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0xf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf as nat
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
    * Starting at 0x12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := Push4(s7, 0x01ffc9a7);
      var s9 := Eq(s8);
      var s10 := Push2(s9, 0x0aff);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s11, gas - 1)
      else
        ExecuteFromCFGNode_s3(s11, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x24
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x8da5cb5b);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0ad1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s264(s6, gas - 1)
      else
        ExecuteFromCFGNode_s4(s6, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x30
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x90659f60);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x08d7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s199(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x9d1978e2);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0356);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x46
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0xc60194ef);
      var s2 := Eq(s1);
      var s3 := Push2(s2, 0x0053);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s8(s4, gas - 1)
      else
        ExecuteFromCFGNode_s7(s4, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x50
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

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
    * Segment Id for this node is: 8
    * Starting at 0x53
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x02ad);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s4, gas - 1)
      else
        ExecuteFromCFGNode_s9(s4, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x59
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0061);
      assert s1.Peek(0) == 0x61;
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x0b52);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s4, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 143
    * Starting at 0xb52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[1] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x61;
      var s2 := Push1(s1, 0x40);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := Not(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x02ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s9, gas - 1)
      else
        ExecuteFromCFGNode_s11(s9, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 144
    * Starting at 0xb5f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(1) == 0x61;
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x61;
      var s12 := Push2(s11, 0x02ad);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s13, gas - 1)
      else
        ExecuteFromCFGNode_s12(s13, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 145
    * Starting at 0xb72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[1] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0x61;
      var s2 := Push1(s1, 0x24);
      var s3 := CallDataLoad(s2);
      var s4 := Push4(s3, 0xffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x02ad);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s10, gas - 1)
      else
        ExecuteFromCFGNode_s13(s10, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 146
    * Starting at 0xb83
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0x61;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s2, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 10
    * Starting at 0x61
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push0(s8);
      var s10 := MStore(s9);
      var s11 := Push0(s10);
      var s12 := Push1(s11, 0x20);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Push0(s14);
      var s16 := Keccak256(s15);
      var s17 := Swap2(s16);
      var s18 := Push4(s17, 0xffffffff);
      var s19 := Swap3(s18);
      var s20 := Dup4(s19);
      var s21 := Dup2(s20);
      var s22 := SLoad(s21);
      var s23 := And(s22);
      var s24 := Dup5(s23);
      var s25 := Dup5(s24);
      var s26 := And(s25);
      var s27 := Lt(s26);
      var s28 := IsZero(s27);
      var s29 := Push2(s28, 0x0344);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s30, gas - 1)
      else
        ExecuteFromCFGNode_s15(s30, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 11
    * Starting at 0x89
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Swap1(s1);
      var s3 := Dup5(s2);
      var s4 := Dup5(s3);
      var s5 := And(s4);
      var s6 := Push0(s5);
      var s7 := MStore(s6);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      var s12 := Push0(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap2(s13);
      var s15 := Dup3(s14);
      var s16 := SLoad(s15);
      var s17 := Push1(s16, 0xff);
      var s18 := Dup2(s17);
      var s19 := And(s18);
      var s20 := Push2(s19, 0x0332);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s21, gas - 1)
      else
        ExecuteFromCFGNode_s16(s21, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 12
    * Starting at 0xa4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup4(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Sub(s8);
      var s10 := Push2(s9, 0x0320);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s11, gas - 1)
      else
        ExecuteFromCFGNode_s17(s11, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 13
    * Starting at 0xb4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Push1(s1, 0xff);
      var s3 := Not(s2);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Or(s5);
      var s7 := Dup5(s6);
      var s8 := SStore(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      var s12 := SLoad(s11);
      var s13 := Push1(s12, 0x03);
      var s14 := Push1(s13, 0x02);
      var s15 := Dup7(s14);
      var s16 := Add(s15);
      var s17 := Swap6(s16);
      var s18 := Add(s17);
      var s19 := SLoad(s18);
      var s20 := Swap5(s19);
      var s21 := Push1(s20, 0x40);
      var s22 := MLoad(s21);
      var s23 := Swap6(s22);
      var s24 := Dup7(s23);
      var s25 := Swap3(s24);
      var s26 := Push4(s25, 0xdabdb389);
      var s27 := Push1(s26, 0xe0);
      var s28 := Shl(s27);
      var s29 := Dup5(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x84);
      var s32 := Dup5(s31);
      var s33 := Add(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x01);
      var s36 := Dup1(s35);
      var s37 := Push1(s36, 0xa0);
      var s38 := Shl(s37);
      var s39 := Sub(s38);
      var s40 := Dup9(s39);
      var s41 := And(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s18(s41, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 14
    * Starting at 0xeb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := Dup7(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x24);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x80);
      var s10 := Push1(s9, 0x44);
      var s11 := Dup6(s10);
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      var s15 := SLoad(s14);
      var s16 := Dup1(s15);
      var s17 := Swap2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0xa4);
      var s20 := Dup5(s19);
      var s21 := Add(s20);
      var s22 := Swap1(s21);
      var s23 := Push1(s22, 0xa4);
      var s24 := Dup2(s23);
      var s25 := Push1(s24, 0x05);
      var s26 := Shl(s25);
      var s27 := Dup7(s26);
      var s28 := Add(s27);
      var s29 := Add(s28);
      var s30 := Swap4(s29);
      var s31 := Push0(s30);
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Push0(s33);
      var s35 := Keccak256(s34);
      var s36 := Swap2(s35);
      var s37 := Push0(s36);
      var s38 := Swap1(s37);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s19(s38, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 15
    * Starting at 0x119
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x02d0);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s6, gas - 1)
      else
        ExecuteFromCFGNode_s20(s6, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 16
    * Starting at 0x121
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x64);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push0(s8);
      var s10 := Swap3(s9);
      var s11 := Swap1(s10);
      var s12 := Dup3(s11);
      var s13 := Swap1(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Dup3(s15);
      var s17 := Swap1(s16);
      var s18 := Dup5(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0xff);
      var s21 := Not(s20);
      var s22 := And(s21);
      var s23 := Push1(s22, 0x01);
      var s24 := Or(s23);
      var s25 := Push1(s24, 0x08);
      var s26 := Shr(s25);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0x01);
      var s29 := Push1(s28, 0xa0);
      var s30 := Shl(s29);
      var s31 := Sub(s30);
      var s32 := And(s31);
      var s33 := Gas(s32);
      var s34 := Call(s33);
      var s35 := Swap4(s34);
      var s36 := Dup5(s35);
      var s37 := IsZero(s36);
      var s38 := Push2(s37, 0x02c5);
      var s39 := JumpI(s38);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s38.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s39, gas - 1)
      else
        ExecuteFromCFGNode_s21(s39, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 17
    * Starting at 0x151
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := Swap4(s1);
      var s3 := Push0(s2);
      var s4 := Swap6(s3);
      var s5 := Push2(s4, 0x01b1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s6, gas - 1)
      else
        ExecuteFromCFGNode_s22(s6, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 18
    * Starting at 0x159
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x159 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Swap4(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      var s12 := And(s11);
      var s13 := Swap3(s12);
      var s14 := Swap1(s13);
      var s15 := Swap2(s14);
      var s16 := And(s15);
      var s17 := Swap1(s16);
      var s18 := Push32(s17, 0x541b022fce588a99d41c70b8fb346dac2c36238eab28353e50a1eb6f12efcfd7);
      var s19 := Swap1(s18);
      var s20 := Dup1(s19);
      var s21 := Push2(s20, 0x019b);
      assert s21.Peek(0) == 0x19b;
      var s22 := Dup9(s21);
      var s23 := Dup9(s22);
      var s24 := Dup4(s23);
      var s25 := Push2(s24, 0x0bcb);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s26, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 153
    * Starting at 0xbcb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x19b;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Dup6(s9);
      var s11 := MStore(s10);
      assert s11.Peek(3) == 0x19b;
      var s12 := Dup1(s11);
      var s13 := MLoad(s12);
      var s14 := Dup1(s13);
      var s15 := Swap3(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x60);
      var s18 := Dup6(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Push1(s20, 0x60);
      assert s21.Peek(5) == 0x19b;
      var s22 := Dup2(s21);
      var s23 := Push1(s22, 0x05);
      var s24 := Shl(s23);
      var s25 := Dup8(s24);
      var s26 := Add(s25);
      var s27 := Add(s26);
      var s28 := Swap2(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Dup1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(7) == 0x19b;
      var s32 := Add(s31);
      var s33 := Swap4(s32);
      var s34 := Push0(s33);
      var s35 := Swap1(s34);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s24(s35, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 154
    * Starting at 0xbf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x19b;
      var s2 := Dup4(s1);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0c08);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s6, gas - 1)
      else
        ExecuteFromCFGNode_s25(s6, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 155
    * Starting at 0xbfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0x19b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Swap4(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s11, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 19
    * Starting at 0x19b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x19b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Sub(s1);
      var s3 := Swap1(s2);
      var s4 := Log4(s3);
      var s5 := Push2(s4, 0x01ad);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Swap3(s7);
      var s9 := Dup4(s8);
      var s10 := Swap3(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(3) == 0x1ad;
      var s12 := Push2(s11, 0x0bcb);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s13, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 153
    * Starting at 0xbcb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1ad;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Dup6(s9);
      var s11 := MStore(s10);
      assert s11.Peek(3) == 0x1ad;
      var s12 := Dup1(s11);
      var s13 := MLoad(s12);
      var s14 := Dup1(s13);
      var s15 := Swap3(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x60);
      var s18 := Dup6(s17);
      var s19 := Add(s18);
      var s20 := Swap2(s19);
      var s21 := Push1(s20, 0x60);
      assert s21.Peek(5) == 0x1ad;
      var s22 := Dup2(s21);
      var s23 := Push1(s22, 0x05);
      var s24 := Shl(s23);
      var s25 := Dup8(s24);
      var s26 := Add(s25);
      var s27 := Add(s26);
      var s28 := Swap2(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Dup1(s29);
      var s31 := Swap2(s30);
      assert s31.Peek(7) == 0x1ad;
      var s32 := Add(s31);
      var s33 := Swap4(s32);
      var s34 := Push0(s33);
      var s35 := Swap1(s34);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s28(s35, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 154
    * Starting at 0xbf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1ad;
      var s2 := Dup4(s1);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0c08);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s6, gas - 1)
      else
        ExecuteFromCFGNode_s29(s6, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 155
    * Starting at 0xbfc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbfc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0x1ad;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Swap4(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s11, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 20
    * Starting at 0x1ad
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Sub(s1);
      var s3 := Swap1(s2);
      var s4 := Return(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 31
    * Segment Id for this node is: 156
    * Starting at 0xc08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[7] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1ad;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := Swap3(s3);
      var s5 := Swap4(s4);
      var s6 := Dup4(s5);
      var s7 := Dup1(s6);
      var s8 := Push2(s7, 0x0c24);
      var s9 := Push1(s8, 0x01);
      var s10 := Swap4(s9);
      var s11 := Push1(s10, 0x5f);
      assert s11.Peek(2) == 0xc24;
      assert s11.Peek(12) == 0x1ad;
      var s12 := Not(s11);
      var s13 := Dup14(s12);
      var s14 := Dup3(s13);
      var s15 := Sub(s14);
      var s16 := Add(s15);
      var s17 := Dup7(s16);
      var s18 := MStore(s17);
      var s19 := Dup10(s18);
      var s20 := MLoad(s19);
      var s21 := Push2(s20, 0x0ba6);
      assert s21.Peek(0) == 0xba6;
      assert s21.Peek(3) == 0xc24;
      assert s21.Peek(13) == 0x1ad;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s22, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 151
    * Starting at 0xba6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0xc24

    requires s0.stack[12] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc24;
      assert s1.Peek(12) == 0x1ad;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap2(s3);
      var s5 := Push2(s4, 0x0bbf);
      var s6 := Dup2(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap3(s8);
      var s10 := Dup2(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(4) == 0xbbf;
      assert s11.Peek(8) == 0xc24;
      assert s11.Peek(18) == 0x1ad;
      var s12 := MStore(s11);
      var s13 := Dup6(s12);
      var s14 := Dup1(s13);
      var s15 := Dup7(s14);
      var s16 := Add(s15);
      var s17 := Swap2(s16);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0b85);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s20, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 147
    * Starting at 0xb85
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0xbbf

    requires s0.stack[7] == 0xc24

    requires s0.stack[17] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbbf;
      assert s1.Peek(7) == 0xc24;
      assert s1.Peek(17) == 0x1ad;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s2, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 148
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xc24

    requires s0.stack[18] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbbf;
      assert s1.Peek(8) == 0xc24;
      assert s1.Peek(18) == 0x1ad;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b96);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s6, gas - 1)
      else
        ExecuteFromCFGNode_s35(s6, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 149
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xc24

    requires s0.stack[18] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0xbbf;
      assert s1.Peek(7) == 0xc24;
      assert s1.Peek(17) == 0x1ad;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s7, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 152
    * Starting at 0xbbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0xc24

    requires s0.stack[13] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc24;
      assert s1.Peek(13) == 0x1ad;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s10, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 157
    * Starting at 0xc24
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[10] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x1ad;
      var s2 := Swap(s1, 8);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap5(s8);
      var s10 := Swap4(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(7) == 0x1ad;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0bf4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s14, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 150
    * Starting at 0xb96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xc24

    requires s0.stack[18] == 0x1ad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbbf;
      assert s1.Peek(8) == 0xc24;
      assert s1.Peek(18) == 0x1ad;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0xbbf;
      assert s11.Peek(8) == 0xc24;
      assert s11.Peek(18) == 0x1ad;
      var s12 := Push2(s11, 0x0b87);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s13, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 156
    * Starting at 0xc08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[7] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x19b;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := Swap3(s3);
      var s5 := Swap4(s4);
      var s6 := Dup4(s5);
      var s7 := Dup1(s6);
      var s8 := Push2(s7, 0x0c24);
      var s9 := Push1(s8, 0x01);
      var s10 := Swap4(s9);
      var s11 := Push1(s10, 0x5f);
      assert s11.Peek(2) == 0xc24;
      assert s11.Peek(12) == 0x19b;
      var s12 := Not(s11);
      var s13 := Dup14(s12);
      var s14 := Dup3(s13);
      var s15 := Sub(s14);
      var s16 := Add(s15);
      var s17 := Dup7(s16);
      var s18 := MStore(s17);
      var s19 := Dup10(s18);
      var s20 := MLoad(s19);
      var s21 := Push2(s20, 0x0ba6);
      assert s21.Peek(0) == 0xba6;
      assert s21.Peek(3) == 0xc24;
      assert s21.Peek(13) == 0x19b;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s22, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 151
    * Starting at 0xba6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0xc24

    requires s0.stack[12] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc24;
      assert s1.Peek(12) == 0x19b;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap2(s3);
      var s5 := Push2(s4, 0x0bbf);
      var s6 := Dup2(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap3(s8);
      var s10 := Dup2(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(4) == 0xbbf;
      assert s11.Peek(8) == 0xc24;
      assert s11.Peek(18) == 0x19b;
      var s12 := MStore(s11);
      var s13 := Dup6(s12);
      var s14 := Dup1(s13);
      var s15 := Dup7(s14);
      var s16 := Add(s15);
      var s17 := Swap2(s16);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0b85);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s20, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 147
    * Starting at 0xb85
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[3] == 0xbbf

    requires s0.stack[7] == 0xc24

    requires s0.stack[17] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbbf;
      assert s1.Peek(7) == 0xc24;
      assert s1.Peek(17) == 0x19b;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s42(s2, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 148
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xc24

    requires s0.stack[18] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbbf;
      assert s1.Peek(8) == 0xc24;
      assert s1.Peek(18) == 0x19b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b96);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s6, gas - 1)
      else
        ExecuteFromCFGNode_s43(s6, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 149
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xc24

    requires s0.stack[18] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0xbbf;
      assert s1.Peek(7) == 0xc24;
      assert s1.Peek(17) == 0x19b;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 152
    * Starting at 0xbbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[3] == 0xc24

    requires s0.stack[13] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc24;
      assert s1.Peek(13) == 0x19b;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s10, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 157
    * Starting at 0xc24
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc24 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[10] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x19b;
      var s2 := Swap(s1, 8);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap5(s8);
      var s10 := Swap4(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(7) == 0x19b;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x0bf4);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s14, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 150
    * Starting at 0xb96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xc24

    requires s0.stack[18] == 0x19b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbbf;
      assert s1.Peek(8) == 0xc24;
      assert s1.Peek(18) == 0x19b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0xbbf;
      assert s11.Peek(8) == 0xc24;
      assert s11.Peek(18) == 0x19b;
      var s12 := Push2(s11, 0x0b87);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s13, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 21
    * Starting at 0x1b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Pop(s2);
      var s4 := Swap4(s3);
      var s5 := Pop(s4);
      var s6 := ReturnDataSize(s5);
      var s7 := Dup1(s6);
      var s8 := Push0(s7);
      var s9 := Dup6(s8);
      var s10 := ReturnDataCopy(s9);
      var s11 := Push2(s10, 0x01c4);
      assert s11.Peek(0) == 0x1c4;
      var s12 := Dup2(s11);
      var s13 := Dup6(s12);
      var s14 := Push2(s13, 0x0c50);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s15, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 160
    * Starting at 0xc50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c4;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup1(s3);
      var s5 := Not(s4);
      var s6 := Swap2(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x1c4;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup3(s14);
      var s16 := Gt(s15);
      var s17 := Or(s16);
      var s18 := Push2(s17, 0x02b1);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s19, gas - 1)
      else
        ExecuteFromCFGNode_s49(s19, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 161
    * Starting at 0xc6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1c4;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s3, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 22
    * Starting at 0x1c4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup2(s5);
      var s7 := Dup6(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := Push2(s9, 0x02ad);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s11, gas - 1)
      else
        ExecuteFromCFGNode_s51(s11, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 23
    * Starting at 0x1d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := MLoad(s1);
      var s3 := Swap4(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Swap5(s4);
      var s6 := Dup6(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := Push2(s8, 0x02ad);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s10, gas - 1)
      else
        ExecuteFromCFGNode_s52(s10, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 24
    * Starting at 0x1e6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Swap6(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x02ad);
      assert s11.Peek(0) == 0x2ad;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s12, gas - 1)
      else
        ExecuteFromCFGNode_s53(s12, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 25
    * Starting at 0x1f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x0200);
      var s4 := Dup2(s3);
      var s5 := Push2(s4, 0x0c72);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 162
    * Starting at 0xc72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x200;
      var s2 := Push8(s1, 0xffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x02b1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s6, gas - 1)
      else
        ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 163
    * Starting at 0xc82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(2) == 0x200;
      var s2 := Shl(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s6, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 26
    * Starting at 0x200
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x200 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 8);
      var s3 := Push2(s2, 0x020e);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Swap(s5, 10);
      var s7 := Dup11(s6);
      var s8 := Push2(s7, 0x0c50);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s9, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 160
    * Starting at 0xc50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20e;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup1(s3);
      var s5 := Not(s4);
      var s6 := Swap2(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x20e;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup3(s14);
      var s16 := Gt(s15);
      var s17 := Or(s16);
      var s18 := Push2(s17, 0x02b1);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s19, gas - 1)
      else
        ExecuteFromCFGNode_s58(s19, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 161
    * Starting at 0xc6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x20e;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s3, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 27
    * Starting at 0x20e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup10(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Dup11(s6);
      var s8 := Add(s7);
      var s9 := Swap3(s8);
      var s10 := Push1(s9, 0x05);
      var s11 := Shl(s10);
      var s12 := Dup6(s11);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := Swap4(s14);
      var s16 := Dup6(s15);
      var s17 := Dup6(s16);
      var s18 := Gt(s17);
      var s19 := Push2(s18, 0x02ad);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s20, gas - 1)
      else
        ExecuteFromCFGNode_s60(s20, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 28
    * Starting at 0x226
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x226 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s61(s4, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 29
    * Starting at 0x22b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup6(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0244);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s6, gas - 1)
      else
        ExecuteFromCFGNode_s62(s6, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 30
    * Starting at 0x233
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x233 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Swap4(s10);
      var s12 := Push0(s11);
      var s13 := Push2(s12, 0x0159);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s14, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 31
    * Starting at 0x244
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Dup6(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := Push2(s6, 0x02ad);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s8, gas - 1)
      else
        ExecuteFromCFGNode_s64(s8, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 32
    * Starting at 0x24e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      var s2 := Add(s1);
      var s3 := Swap1(s2);
      var s4 := Dup8(s3);
      var s5 := Push1(s4, 0x3f);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x02ad);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s11, gas - 1)
      else
        ExecuteFromCFGNode_s65(s11, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 33
    * Starting at 0x25c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Dup7(s5);
      var s7 := Dup3(s6);
      var s8 := Gt(s7);
      var s9 := Push2(s8, 0x02b1);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s10, gas - 1)
      else
        ExecuteFromCFGNode_s66(s10, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 34
    * Starting at 0x269
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x027e);
      var s4 := Dup4(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x27e;
      var s12 := Dup3(s11);
      var s13 := Push2(s12, 0x0c50);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s14, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 160
    * Starting at 0xc50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x27e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x27e;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup1(s3);
      var s5 := Not(s4);
      var s6 := Swap2(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x27e;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup3(s14);
      var s16 := Gt(s15);
      var s17 := Or(s16);
      var s18 := Push2(s17, 0x02b1);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s19, gas - 1)
      else
        ExecuteFromCFGNode_s68(s19, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 161
    * Starting at 0xc6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x27e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x27e;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s3, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 35
    * Starting at 0x27e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup10(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Dup5(s6);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      var s12 := Push2(s11, 0x02ad);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s13, gas - 1)
      else
        ExecuteFromCFGNode_s70(s13, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 36
    * Starting at 0x28e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02a2);
      assert s1.Peek(0) == 0x2a2;
      var s2 := Push1(s1, 0x20);
      var s3 := Swap5(s2);
      var s4 := Swap4(s3);
      var s5 := Dup6(s4);
      var s6 := Swap5(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Dup7(s7);
      var s9 := Dup6(s8);
      var s10 := Add(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(4) == 0x2a2;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x0b85);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s14, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 147
    * Starting at 0xb85
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x2a2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2a2;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s72(s2, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 148
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x2a2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2a2;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b96);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s6, gas - 1)
      else
        ExecuteFromCFGNode_s73(s6, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 149
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x2a2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x2a2;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s7, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 37
    * Starting at 0x2a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Add(s3);
      var s5 := Swap4(s4);
      var s6 := Add(s5);
      var s7 := Swap3(s6);
      var s8 := Push2(s7, 0x022b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s9, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 150
    * Starting at 0xb96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x2a2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2a2;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x2a2;
      var s12 := Push2(s11, 0x0b87);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s13, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

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

  /** Node 77
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x27e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x27e;
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
      assert s11.Peek(3) == 0x27e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 78
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

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
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 79
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

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

  /** Node 80
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

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

  /** Node 81
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x20e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x20e;
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
      assert s11.Peek(3) == 0x20e;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 82
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x200

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x200;
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
      assert s11.Peek(3) == 0x200;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 83
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

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

  /** Node 84
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

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

  /** Node 85
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

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

  /** Node 86
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x1c4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c4;
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
      assert s11.Peek(3) == 0x1c4;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 87
    * Segment Id for this node is: 40
    * Starting at 0x2c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := ReturnDataSize(s3);
      var s5 := Push0(s4);
      var s6 := Dup3(s5);
      var s7 := ReturnDataCopy(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Swap1(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 88
    * Segment Id for this node is: 41
    * Starting at 0x2d0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap2(s1);
      var s3 := Swap4(s2);
      var s4 := Swap5(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push2(s5, 0x030f);
      var s7 := Push1(s6, 0x20);
      var s8 := Swap3(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Swap5(s9);
      var s11 := Swap7(s10);
      assert s11.Peek(2) == 0x30f;
      var s12 := Swap(s11, 10);
      var s13 := Push1(s12, 0xa3);
      var s14 := Not(s13);
      var s15 := Swap1(s14);
      var s16 := Dup3(s15);
      var s17 := Sub(s16);
      var s18 := Add(s17);
      var s19 := Dup7(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x60);
      assert s21.Peek(2) == 0x30f;
      var s22 := Swap1(s21);
      var s23 := Dup6(s22);
      var s24 := Dup1(s23);
      var s25 := Push1(s24, 0xa0);
      var s26 := Shl(s25);
      var s27 := Sub(s26);
      var s28 := Dup12(s27);
      var s29 := SLoad(s28);
      var s30 := And(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(4) == 0x30f;
      var s32 := MStore(s31);
      var s33 := Dup6(s32);
      var s34 := Dup12(s33);
      var s35 := Add(s34);
      var s36 := SLoad(s35);
      var s37 := Dup6(s36);
      var s38 := Dup3(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := Dup2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s89(s41, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 42
    * Starting at 0x301
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x301 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x30f;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Dup11(s6);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0cc2);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s10, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 169
    * Starting at 0xcc2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x30f;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push0(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Push2(s6, 0x0cd0);
      var s8 := Dup3(s7);
      var s9 := Push2(s8, 0x0c8a);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s10, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 164
    * Starting at 0xc8a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0xcd0

    requires s0.stack[5] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd0;
      assert s1.Peek(5) == 0x30f;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Shr(s5);
      var s7 := Swap3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0cb8);
      assert s11.Peek(0) == 0xcb8;
      assert s11.Peek(3) == 0xcd0;
      assert s11.Peek(8) == 0x30f;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s12, gas - 1)
      else
        ExecuteFromCFGNode_s92(s12, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 165
    * Starting at 0xc99
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xcd0

    requires s0.stack[6] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd0;
      assert s1.Peek(6) == 0x30f;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0ca4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s7, gas - 1)
      else
        ExecuteFromCFGNode_s93(s7, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 166
    * Starting at 0xca3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xcd0

    requires s0.stack[5] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s1, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 170
    * Starting at 0xcd0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x30f;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap4(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x30f;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push0(s14);
      var s16 := Eq(s15);
      var s17 := Push2(s16, 0x0d34);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s18, gas - 1)
      else
        ExecuteFromCFGNode_s95(s18, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 171
    * Starting at 0xce7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0x30f;
      var s2 := Push1(s1, 0x01);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0cf6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s5, gas - 1)
      else
        ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 172
    * Starting at 0xcef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x30f;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s7, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 43
    * Starting at 0x30f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 8);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Add(s6);
      var s8 := Dup10(s7);
      var s9 := Swap6(s8);
      var s10 := Swap5(s9);
      var s11 := Swap4(s10);
      var s12 := Swap2(s11);
      var s13 := Swap3(s12);
      var s14 := Push2(s13, 0x0119);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s15, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 173
    * Starting at 0xcf6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x30f;
      var s2 := Swap1(s1);
      var s3 := Swap4(s2);
      var s4 := Swap5(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Push0(s6);
      var s8 := Swap3(s7);
      var s9 := Swap2(s8);
      var s10 := Swap3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0x30f;
      var s12 := Dup4(s11);
      var s13 := Push0(s12);
      var s14 := Keccak256(s13);
      var s15 := Swap3(s14);
      var s16 := Dup5(s15);
      var s17 := Push0(s16);
      var s18 := Swap5(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s99(s18, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 174
    * Starting at 0xd08
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x30f;
      var s2 := Dup4(s1);
      var s3 := Dup7(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0d20);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s6, gas - 1)
      else
        ExecuteFromCFGNode_s100(s6, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 175
    * Starting at 0xd10
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0x30f;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Push0(s7);
      var s9 := Dup1(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x30f;
      var s12 := Dup1(s11);
      var s13 := Push2(s12, 0x0cef);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s14, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 176
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x30f;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Dup6(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x30f;
      var s12 := Swap4(s11);
      var s13 := Dup6(s12);
      var s14 := Swap1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0d08);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s18, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 177
    * Starting at 0xd34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x30f;
      var s2 := Push1(s1, 0xff);
      var s3 := Not(s2);
      var s4 := And(s3);
      var s5 := Dup7(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0x30f;
      var s12 := Swap1(s11);
      var s13 := IsZero(s12);
      var s14 := IsZero(s13);
      var s15 := Push1(s14, 0x05);
      var s16 := Shl(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap2(s18);
      var s20 := Pop(s19);
      var s21 := Push0(s20);
      assert s21.Peek(1) == 0x30f;
      var s22 := Dup1(s21);
      var s23 := Dup1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup1(s24);
      var s26 := Push2(s25, 0x0cef);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s27, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 167
    * Starting at 0xca4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0xcd0

    requires s0.stack[5] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcd0;
      assert s1.Peek(5) == 0x30f;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x22);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0xcd0;
      assert s11.Peek(7) == 0x30f;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 104
    * Segment Id for this node is: 168
    * Starting at 0xcb8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0xcd0

    requires s0.stack[6] == 0x30f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd0;
      assert s1.Peek(6) == 0x30f;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x7f);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Push2(s5, 0x0c99);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s7, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 44
    * Starting at 0x320
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x320 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x18ce0797);
      var s5 := Push1(s4, 0xe2);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Swap1(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 106
    * Segment Id for this node is: 45
    * Starting at 0x332
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x332 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x6b78fca3);
      var s5 := Push1(s4, 0xe1);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Swap1(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 107
    * Segment Id for this node is: 46
    * Starting at 0x344
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x7037cbb5);
      var s5 := Push1(s4, 0xe1);
      var s6 := Shl(s5);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Swap1(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 108
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 109
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[1] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 110
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x61

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x61;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 111
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
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

  /** Node 112
    * Segment Id for this node is: 47
    * Starting at 0x356
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x356 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x02ad);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s4, gas - 1)
      else
        ExecuteFromCFGNode_s113(s4, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 48
    * Starting at 0x35c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0xa0);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x02ad);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s8, gas - 1)
      else
        ExecuteFromCFGNode_s114(s8, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 49
    * Starting at 0x368
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Swap1(s9);
      var s11 := Sub(s10);
      var s12 := Push2(s11, 0x02ad);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s13, gas - 1)
      else
        ExecuteFromCFGNode_s115(s13, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 50
    * Starting at 0x37b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0xffffffffffffffff);
      var s2 := Push1(s1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x02ad);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s6, gas - 1)
      else
        ExecuteFromCFGNode_s116(s6, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 51
    * Starting at 0x38c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataSize(s0);
      var s2 := Push1(s1, 0x23);
      var s3 := Push1(s2, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x02ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s9, gas - 1)
      else
        ExecuteFromCFGNode_s117(s9, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 52
    * Starting at 0x399
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x399 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0xffffffffffffffff);
      var s2 := Push1(s1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x02ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s9, gas - 1)
      else
        ExecuteFromCFGNode_s118(s9, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 53
    * Starting at 0x3ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataSize(s0);
      var s2 := Push1(s1, 0x24);
      var s3 := Push1(s2, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push1(s7, 0x05);
      var s9 := Shl(s8);
      var s10 := Push1(s9, 0x44);
      var s11 := CallDataLoad(s10);
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x02ad);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s16, gas - 1)
      else
        ExecuteFromCFGNode_s119(s16, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 54
    * Starting at 0x3c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0xffffffffffffffff);
      var s2 := Push1(s1, 0x84);
      var s3 := CallDataLoad(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x02ad);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s6, gas - 1)
      else
        ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 55
    * Starting at 0x3d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataSize(s0);
      var s2 := Push1(s1, 0x23);
      var s3 := Push1(s2, 0x84);
      var s4 := CallDataLoad(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x02ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s9, gas - 1)
      else
        ExecuteFromCFGNode_s121(s9, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 56
    * Starting at 0x3e3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0xffffffffffffffff);
      var s2 := Push1(s1, 0x84);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x02ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s9, gas - 1)
      else
        ExecuteFromCFGNode_s122(s9, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 57
    * Starting at 0x3f8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := CallDataSize(s0);
      var s2 := Push1(s1, 0x24);
      var s3 := Push1(s2, 0x84);
      var s4 := CallDataLoad(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push1(s7, 0x84);
      var s9 := CallDataLoad(s8);
      var s10 := Add(s9);
      var s11 := Add(s10);
      var s12 := Gt(s11);
      var s13 := Push2(s12, 0x02ad);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s14, gas - 1)
      else
        ExecuteFromCFGNode_s123(s14, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 58
    * Starting at 0x40c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      var s2 := Push0(s1);
      var s3 := MStore(s2);
      var s4 := Push0(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Push0(s7);
      var s9 := Keccak256(s8);
      var s10 := Dup1(s9);
      var s11 := SLoad(s10);
      var s12 := Swap1(s11);
      var s13 := Push4(s12, 0xffffffff);
      var s14 := Dup1(s13);
      var s15 := Dup4(s14);
      var s16 := And(s15);
      var s17 := Eq(s16);
      var s18 := Push2(s17, 0x08c3);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s19, gas - 1)
      else
        ExecuteFromCFGNode_s124(s19, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 59
    * Starting at 0x427
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x427 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Swap1(s1);
      var s3 := Push4(s2, 0xffffffff);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Dup6(s5);
      var s7 := And(s6);
      var s8 := Add(s7);
      var s9 := And(s8);
      var s10 := Push4(s9, 0xffffffff);
      var s11 := Not(s10);
      var s12 := Dup5(s11);
      var s13 := And(s12);
      var s14 := Or(s13);
      var s15 := Dup2(s14);
      var s16 := SStore(s15);
      var s17 := Push4(s16, 0xffffffff);
      var s18 := Dup4(s17);
      var s19 := And(s18);
      var s20 := Push0(s19);
      var s21 := MStore(s20);
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x20);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := Push0(s25);
      var s27 := Keccak256(s26);
      var s28 := Dup1(s27);
      var s29 := SLoad(s28);
      var s30 := Push2(s29, 0x0100);
      var s31 := Push1(s30, 0x01);
      var s32 := Push1(s31, 0xa8);
      var s33 := Shl(s32);
      var s34 := Sub(s33);
      var s35 := Push1(s34, 0x04);
      var s36 := CallDataLoad(s35);
      var s37 := Push1(s36, 0x08);
      var s38 := Shl(s37);
      var s39 := And(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x0100);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s125(s41, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 60
    * Starting at 0x467
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x467 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Push1(s1, 0xa8);
      var s3 := Shl(s2);
      var s4 := Sub(s3);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Or(s6);
      var s8 := Dup2(s7);
      var s9 := SStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := CallDataLoad(s10);
      var s12 := Push1(s11, 0x01);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := SStore(s14);
      var s16 := PushN(s15, 9, 0x010000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := CallDataLoad(s17);
      var s19 := Push1(s18, 0x04);
      var s20 := Add(s19);
      var s21 := CallDataLoad(s20);
      var s22 := Gt(s21);
      var s23 := Push2(s22, 0x02b1);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s24, gas - 1)
      else
        ExecuteFromCFGNode_s126(s24, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 61
    * Starting at 0x490
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x490 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push1(s6, 0x44);
      var s8 := CallDataLoad(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap2(s10);
      var s12 := Dup3(s11);
      var s13 := Swap1(s12);
      var s14 := SStore(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := Gt(s16);
      var s18 := Push2(s17, 0x080e);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s19, gas - 1)
      else
        ExecuteFromCFGNode_s127(s19, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 62
    * Starting at 0x4a8
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x24);
      var s4 := Push1(s3, 0x44);
      var s5 := CallDataLoad(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push0(s9);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x20);
      var s13 := Push0(s12);
      var s14 := Keccak256(s13);
      var s15 := Push0(s14);
      var s16 := Swap2(s15);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s128(s16, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 63
    * Starting at 0x4bc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup4(s6);
      var s8 := Lt(s7);
      var s9 := Push2(s8, 0x0634);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s10, gas - 1)
      else
        ExecuteFromCFGNode_s129(s10, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 64
    * Starting at 0x4ca
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x64);
      var s5 := CallDataLoad(s4);
      var s6 := Push1(s5, 0x03);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := SStore(s10);
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := MLoad(s13);
      var s15 := Push1(s14, 0x04);
      var s16 := Dup1(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Push1(s17, 0x01);
      var s19 := Push1(s18, 0x01);
      var s20 := Push1(s19, 0xa0);
      var s21 := Shl(s20);
      var s22 := Sub(s21);
      var s23 := And(s22);
      var s24 := Dup3(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x24);
      var s27 := Dup1(s26);
      var s28 := CallDataLoad(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Dup5(s29);
      var s31 := Add(s30);
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0xa0);
      var s34 := Swap4(s33);
      var s35 := Dup4(s34);
      var s36 := Add(s35);
      var s37 := Dup5(s36);
      var s38 := Swap1(s37);
      var s39 := MStore(s38);
      var s40 := Push1(s39, 0x44);
      var s41 := CallDataLoad(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s130(s41, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 65
    * Starting at 0x4fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap4(s4);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := Dup5(s7);
      var s9 := Swap1(s8);
      var s10 := MStore(s9);
      var s11 := Add(s10);
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Push1(s13, 0x05);
      var s15 := Shl(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0xc0);
      var s19 := Swap1(s18);
      var s20 := Dup2(s19);
      var s21 := Add(s20);
      var s22 := Swap1(s21);
      var s23 := Push0(s22);
      var s24 := Swap1(s23);
      var s25 := Dup4(s24);
      var s26 := Add(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s131(s26, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 66
    * Starting at 0x51a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup3(s6);
      var s8 := Lt(s7);
      var s9 := Push2(s8, 0x058f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s10, gas - 1)
      else
        ExecuteFromCFGNode_s132(s10, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 67
    * Starting at 0x528
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x528 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap4(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x64);
      var s7 := CallDataLoad(s6);
      var s8 := Push1(s7, 0x60);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      var s12 := Dup2(s11);
      var s13 := Dup2(s12);
      var s14 := Sub(s13);
      var s15 := Push1(s14, 0x80);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0xb3a13e1e0c8b5e4c085d2e688e22dce8174e51ffbb2492a4231140eddb2b91a9);
      var s20 := Caller(s19);
      var s21 := Swap3(s20);
      var s22 := Dup1(s21);
      var s23 := Push2(s22, 0x057e);
      var s24 := Push4(s23, 0xffffffff);
      var s25 := Dup8(s24);
      var s26 := And(s25);
      var s27 := Swap5(s26);
      var s28 := Push1(s27, 0x84);
      var s29 := CallDataLoad(s28);
      var s30 := Push1(s29, 0x04);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x57e;
      var s32 := CallDataLoad(s31);
      var s33 := Push1(s32, 0x24);
      var s34 := Push1(s33, 0x84);
      var s35 := CallDataLoad(s34);
      var s36 := Add(s35);
      var s37 := Push2(s36, 0x0d69);
      var s38 := Jump(s37);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s38, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 181
    * Starting at 0xd69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x57e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x57e;
      var s2 := Swap1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Dup2(s6);
      var s8 := Dup5(s7);
      var s9 := MStore(s8);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(7) == 0x57e;
      var s12 := Add(s11);
      var s13 := CallDataCopy(s12);
      var s14 := Push0(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Dup5(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x1f);
      assert s21.Peek(4) == 0x57e;
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x1f);
      var s24 := Not(s23);
      var s25 := And(s24);
      var s26 := Add(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s29, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 68
    * Starting at 0x57e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Sub(s1);
      var s3 := Swap1(s2);
      var s4 := Log3(s3);
      var s5 := Push4(s4, 0xffffffff);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Swap2(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      var s12 := Return(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 135
    * Segment Id for this node is: 69
    * Starting at 0x58f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Sub(s3);
      var s5 := Push1(s4, 0xbf);
      var s6 := Not(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      var s12 := Dup6(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Push1(s13, 0x44);
      var s15 := CallDataLoad(s14);
      var s16 := CallDataSize(s15);
      var s17 := Sub(s16);
      var s18 := Push1(s17, 0x82);
      var s19 := Not(s18);
      var s20 := Add(s19);
      var s21 := Dup2(s20);
      var s22 := SLt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x02ad);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s25, gas - 1)
      else
        ExecuteFromCFGNode_s136(s25, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 70
    * Starting at 0x5ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x60);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x24);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := Dup2(s14);
      var s16 := And(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Swap1(s18);
      var s20 := Sub(s19);
      var s21 := Push2(s20, 0x02ad);
      assert s21.Peek(0) == 0x2ad;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s22, gas - 1)
      else
        ExecuteFromCFGNode_s137(s22, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 71
    * Starting at 0x5cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x44);
      var s4 := Dup2(s3);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x64);
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Push1(s14, 0x42);
      var s16 := Not(s15);
      var s17 := Dup3(s16);
      var s18 := CallDataSize(s17);
      var s19 := Sub(s18);
      var s20 := Add(s19);
      var s21 := Dup2(s20);
      var s22 := SLt(s21);
      var s23 := IsZero(s22);
      var s24 := Push2(s23, 0x02ad);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s25, gas - 1)
      else
        ExecuteFromCFGNode_s138(s25, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 72
    * Starting at 0x5ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x44);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap3(s7);
      var s9 := Add(s8);
      var s10 := Swap3(s9);
      var s11 := Push8(s10, 0xffffffffffffffff);
      var s12 := Dup4(s11);
      var s13 := Gt(s12);
      var s14 := Push2(s13, 0x02ad);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s15, gas - 1)
      else
        ExecuteFromCFGNode_s139(s15, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 73
    * Starting at 0x605
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x605 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      var s2 := CallDataSize(s1);
      var s3 := Sub(s2);
      var s4 := Dup5(s3);
      var s5 := SGt(s4);
      var s6 := Push2(s5, 0x02ad);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s7, gas - 1)
      else
        ExecuteFromCFGNode_s140(s7, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 74
    * Starting at 0x60e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Swap4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap4(s3);
      var s5 := Dup4(s4);
      var s6 := Dup4(s5);
      var s7 := Dup7(s6);
      var s8 := Swap6(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Push2(s9, 0x0626);
      var s11 := Swap7(s10);
      assert s11.Peek(7) == 0x626;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Swap2(s14);
      var s16 := Push2(s15, 0x0d69);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s17, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 181
    * Starting at 0xd69
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd69 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x626

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x626;
      var s2 := Swap1(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Dup2(s6);
      var s8 := Dup5(s7);
      var s9 := MStore(s8);
      var s10 := Dup5(s9);
      var s11 := Dup5(s10);
      assert s11.Peek(7) == 0x626;
      var s12 := Add(s11);
      var s13 := CallDataCopy(s12);
      var s14 := Push0(s13);
      var s15 := Dup3(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Dup5(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x1f);
      assert s21.Peek(4) == 0x626;
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x1f);
      var s24 := Not(s23);
      var s25 := And(s24);
      var s26 := Add(s25);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s29, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 75
    * Starting at 0x626
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x626 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap(s1, 8);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap5(s8);
      var s10 := Swap2(s9);
      var s11 := Push2(s10, 0x051a);
      assert s11.Peek(0) == 0x51a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s12, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 38
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
    requires s0.Operands() >= 10

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

  /** Node 144
    * Segment Id for this node is: 76
    * Starting at 0x634
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x634 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x44);
      var s5 := CallDataLoad(s4);
      var s6 := CallDataSize(s5);
      var s7 := Sub(s6);
      var s8 := Push1(s7, 0x82);
      var s9 := Not(s8);
      var s10 := Add(s9);
      var s11 := Dup2(s10);
      var s12 := SLt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x02ad);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s15, gas - 1)
      else
        ExecuteFromCFGNode_s145(s15, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 77
    * Starting at 0x647
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x647 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x44);
      var s2 := CallDataLoad(s1);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x24);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0xa0);
      var s11 := Shl(s10);
      var s12 := Sub(s11);
      var s13 := Dup2(s12);
      var s14 := And(s13);
      var s15 := Swap1(s14);
      var s16 := Dup2(s15);
      var s17 := Swap1(s16);
      var s18 := Sub(s17);
      var s19 := Push2(s18, 0x02ad);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s20, gas - 1)
      else
        ExecuteFromCFGNode_s146(s20, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 78
    * Starting at 0x662
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x662 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Not(s7);
      var s9 := And(s8);
      var s10 := Or(s9);
      var s11 := Dup4(s10);
      var s12 := SStore(s11);
      var s13 := Push1(s12, 0x44);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := CallDataLoad(s15);
      var s17 := Push1(s16, 0x01);
      var s18 := Dup5(s17);
      var s19 := Add(s18);
      var s20 := SStore(s19);
      var s21 := Push1(s20, 0x64);
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := CallDataLoad(s23);
      var s25 := Swap1(s24);
      var s26 := CallDataSize(s25);
      var s27 := Dup2(s26);
      var s28 := Swap1(s27);
      var s29 := Sub(s28);
      var s30 := Push1(s29, 0x42);
      var s31 := Not(s30);
      var s32 := Add(s31);
      var s33 := Dup3(s32);
      var s34 := SLt(s33);
      var s35 := IsZero(s34);
      var s36 := Push2(s35, 0x02ad);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s37, gas - 1)
      else
        ExecuteFromCFGNode_s147(s37, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 79
    * Starting at 0x690
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x690 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0xffffffffffffffff);
      var s2 := Push1(s1, 0x24);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Gt(s7);
      var s9 := Push2(s8, 0x02ad);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s10, gas - 1)
      else
        ExecuteFromCFGNode_s148(s10, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 80
    * Starting at 0x6a5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x24);
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := CallDataSize(s6);
      var s8 := Sub(s7);
      var s9 := Push1(s8, 0x44);
      var s10 := Dup4(s9);
      var s11 := Dup4(s10);
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := SGt(s13);
      var s15 := Push2(s14, 0x02ad);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s16, gas - 1)
      else
        ExecuteFromCFGNode_s149(s16, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 81
    * Starting at 0x6b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06c5);
      assert s1.Peek(0) == 0x6c5;
      var s2 := Push1(s1, 0x02);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0c8a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s7, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 164
    * Starting at 0xc8a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x6c5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6c5;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Shr(s5);
      var s7 := Swap3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0cb8);
      assert s11.Peek(0) == 0xcb8;
      assert s11.Peek(3) == 0x6c5;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s12, gas - 1)
      else
        ExecuteFromCFGNode_s151(s12, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 165
    * Starting at 0xc99
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x6c5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6c5;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0ca4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s7, gas - 1)
      else
        ExecuteFromCFGNode_s152(s7, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 166
    * Starting at 0xca3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x6c5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s1, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 82
    * Starting at 0x6c5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Swap2(s3);
      var s5 := Dup3(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x07c7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s9, gas - 1)
      else
        ExecuteFromCFGNode_s154(s9, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 83
    * Starting at 0x6d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Swap2(s3);
      var s5 := Push1(s4, 0x24);
      var s6 := Dup5(s5);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Gt(s10);
      var s12 := Push1(s11, 0x01);
      var s13 := Eq(s12);
      var s14 := Push2(s13, 0x0733);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s15, gas - 1)
      else
        ExecuteFromCFGNode_s155(s15, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 84
    * Starting at 0x6e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap3(s0);
      var s2 := Push1(s1, 0x03);
      var s3 := Swap3(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Swap3(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap6(s6);
      var s8 := Push0(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Dup5(s10);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := CallDataLoad(s14);
      var s16 := Push2(s15, 0x0723);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s17, gas - 1)
      else
        ExecuteFromCFGNode_s156(s17, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 85
    * Starting at 0x6fb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Swap3(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Dup7(s10);
      var s12 := Shl(s11);
      var s13 := Swap3(s12);
      var s14 := Swap1(s13);
      var s15 := Swap3(s14);
      var s16 := Shr(s15);
      var s17 := Not(s16);
      var s18 := And(s17);
      var s19 := Swap1(s18);
      var s20 := Dup6(s19);
      var s21 := Shl(s20);
      var s22 := Or(s21);
      var s23 := Push1(s22, 0x02);
      var s24 := Dup7(s23);
      var s25 := Add(s24);
      var s26 := SStore(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s157(s26, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 86
    * Starting at 0x717
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x717 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Add(s1);
      var s3 := Swap3(s2);
      var s4 := Add(s3);
      var s5 := Swap3(s4);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Push2(s8, 0x04bc);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s10, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 87
    * Starting at 0x723
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x44);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Swap2(s8);
      var s10 := Pop(s9);
      var s11 := Dup12(s10);
      var s12 := Push2(s11, 0x06fb);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s13, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 88
    * Starting at 0x733
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x733 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := Dup6(s3);
      var s5 := Add(s4);
      var s6 := Push0(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push0(s8);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      var s12 := Push0(s11);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s160(s12, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 89
    * Starting at 0x741
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x741 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x24);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      var s12 := Lt(s11);
      var s13 := Push2(s12, 0x07aa);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s14, gas - 1)
      else
        ExecuteFromCFGNode_s161(s14, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 90
    * Starting at 0x753
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x753 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Push1(s1, 0x01);
      var s3 := Swap5(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := Swap5(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap5(s6);
      var s8 := Swap2(s7);
      var s9 := Swap4(s8);
      var s10 := Dup8(s9);
      var s11 := Swap4(s10);
      var s12 := Push1(s11, 0x24);
      var s13 := Swap4(s12);
      var s14 := Swap2(s13);
      var s15 := Swap1(s14);
      var s16 := Dup3(s15);
      var s17 := Dup5(s16);
      var s18 := Add(s17);
      var s19 := Dup6(s18);
      var s20 := Add(s19);
      var s21 := CallDataLoad(s20);
      var s22 := Push1(s21, 0x1f);
      var s23 := Not(s22);
      var s24 := Dup2(s23);
      var s25 := And(s24);
      var s26 := Lt(s25);
      var s27 := Push2(s26, 0x0788);
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s28, gas - 1)
      else
        ExecuteFromCFGNode_s162(s28, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 91
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Add(s3);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup2(s6);
      var s8 := Shl(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x02);
      var s11 := Dup7(s10);
      var s12 := Add(s11);
      var s13 := SStore(s12);
      var s14 := Push2(s13, 0x0717);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s15, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 92
    * Starting at 0x788
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 15
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x788 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x44);
      var s3 := Push0(s2);
      var s4 := Not(s3);
      var s5 := Push1(s4, 0xf8);
      var s6 := Dup8(s5);
      var s7 := Dup8(s6);
      var s8 := Dup8(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := CallDataLoad(s10);
      var s12 := Dup13(s11);
      var s13 := Shl(s12);
      var s14 := And(s13);
      var s15 := Shr(s14);
      var s16 := Not(s15);
      var s17 := Swap2(s16);
      var s18 := Dup6(s17);
      var s19 := Dup6(s18);
      var s20 := Add(s19);
      var s21 := Add(s20);
      var s22 := Add(s21);
      var s23 := CallDataLoad(s22);
      var s24 := And(s23);
      var s25 := Swap1(s24);
      var s26 := SStore(s25);
      var s27 := Dup13(s26);
      var s28 := Dup1(s27);
      var s29 := Push2(s28, 0x0776);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s30, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 93
    * Starting at 0x7aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push1(s4, 0x01);
      var s6 := Dup2(s5);
      var s7 := Swap3(s6);
      var s8 := Push1(s7, 0x44);
      var s9 := Dup7(s8);
      var s10 := Dup10(s9);
      var s11 := Dup10(s10);
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Add(s13);
      var s15 := CallDataLoad(s14);
      var s16 := Dup2(s15);
      var s17 := SStore(s16);
      var s18 := Add(s17);
      var s19 := Swap4(s18);
      var s20 := Add(s19);
      var s21 := Swap2(s20);
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0741);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s24, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 94
    * Starting at 0x7c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x07ff);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push0(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push0(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(2) == 0x7ff;
      var s12 := Dup5(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup9(s14);
      var s16 := Dup8(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := CallDataLoad(s18);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x05);
      assert s21.Peek(5) == 0x7ff;
      var s22 := Shr(s21);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := Swap3(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Push1(s26, 0x24);
      var s28 := Dup10(s27);
      var s29 := Dup9(s28);
      var s30 := Add(s29);
      var s31 := Add(s30);
      assert s31.Peek(6) == 0x7ff;
      var s32 := CallDataLoad(s31);
      var s33 := Lt(s32);
      var s34 := Push2(s33, 0x0805);
      var s35 := JumpI(s34);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s34.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s35, gas - 1)
      else
        ExecuteFromCFGNode_s166(s35, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 95
    * Starting at 0x7f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x7ff

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7ff;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shr(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0d53);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s8, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 178
    * Starting at 0xd53
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x7ff

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7ff;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0d5e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s6, gas - 1)
      else
        ExecuteFromCFGNode_s168(s6, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 179
    * Starting at 0xd5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x7ff

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x7ff;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s3, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 96
    * Starting at 0x7ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Push2(s2, 0x06d1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s4, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 180
    * Starting at 0xd5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x7ff

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7ff;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := SStore(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0d53);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s8, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 97
    * Starting at 0x805
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x805 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x7ff

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7ff;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Dup2(s3);
      var s5 := Swap3(s4);
      var s6 := Push2(s5, 0x07f4);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s7, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 167
    * Starting at 0xca4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x6c5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6c5;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x22);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x6c5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 173
    * Segment Id for this node is: 168
    * Starting at 0xcb8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x6c5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x6c5;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x7f);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Push2(s5, 0x0c99);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s7, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 98
    * Starting at 0x80e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x03);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Mul(s4);
      var s6 := Div(s5);
      var s7 := Dup2(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x08c3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s10, gas - 1)
      else
        ExecuteFromCFGNode_s175(s10, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 99
    * Starting at 0x81b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x81b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x03);
      var s2 := Push1(s1, 0x44);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := Add(s4);
      var s6 := CallDataLoad(s5);
      var s7 := Dup2(s6);
      var s8 := Mul(s7);
      var s9 := Div(s8);
      var s10 := Push1(s9, 0x44);
      var s11 := CallDataLoad(s10);
      var s12 := Push1(s11, 0x04);
      var s13 := Add(s12);
      var s14 := CallDataLoad(s13);
      var s15 := Sub(s14);
      var s16 := Push2(s15, 0x08c3);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s17, gas - 1)
      else
        ExecuteFromCFGNode_s176(s17, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 100
    * Starting at 0x833
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x833 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Push0(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push0(s6);
      var s8 := Keccak256(s7);
      var s9 := Push1(s8, 0x44);
      var s10 := CallDataLoad(s9);
      var s11 := Push1(s10, 0x04);
      var s12 := Add(s11);
      var s13 := CallDataLoad(s12);
      var s14 := Push1(s13, 0x03);
      var s15 := Mul(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s177(s17, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 101
    * Starting at 0x849
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x849 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Mul(s3);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Dup2(s6);
      var s8 := Lt(s7);
      var s9 := Push2(s8, 0x085c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s10, gas - 1)
      else
        ExecuteFromCFGNode_s178(s10, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 102
    * Starting at 0x856
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x856 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x04a8);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s4, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 103
    * Starting at 0x85c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := Swap3(s4);
      var s6 := SStore(s5);
      var s7 := Push0(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := SStore(s10);
      var s12 := Push1(s11, 0x02);
      var s13 := Dup2(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0876);
      var s16 := Dup2(s15);
      var s17 := SLoad(s16);
      var s18 := Push2(s17, 0x0c8a);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s19, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 164
    * Starting at 0xc8a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x876

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x876;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Shr(s5);
      var s7 := Swap3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0cb8);
      assert s11.Peek(0) == 0xcb8;
      assert s11.Peek(3) == 0x876;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s12, gas - 1)
      else
        ExecuteFromCFGNode_s181(s12, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 165
    * Starting at 0xc99
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x876

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x876;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0ca4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s7, gas - 1)
      else
        ExecuteFromCFGNode_s182(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 166
    * Starting at 0xca3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x876

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s1, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 104
    * Starting at 0x876
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x876 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0885);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s5, gas - 1)
      else
        ExecuteFromCFGNode_s184(s5, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 105
    * Starting at 0x87d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Add(s3);
      var s5 := Push2(s4, 0x0849);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 106
    * Starting at 0x885
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x885 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push0(s1);
      var s3 := Swap2(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Eq(s8);
      var s10 := Push2(s9, 0x089e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s11, gas - 1)
      else
        ExecuteFromCFGNode_s186(s11, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 107
    * Starting at 0x894
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x894 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := SStore(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s187(s3, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 108
    * Starting at 0x897
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x897 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup7(s1);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x087d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s5, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 109
    * Starting at 0x89e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap2(s1);
      var s3 := Push2(s2, 0x08bc);
      var s4 := Dup5(s3);
      var s5 := Swap3(s4);
      var s6 := Swap4(s5);
      var s7 := Dup3(s6);
      var s8 := Dup5(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup5(s10);
      assert s11.Peek(3) == 0x8bc;
      var s12 := Keccak256(s11);
      var s13 := Swap5(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x05);
      var s16 := Shr(s15);
      var s17 := Dup5(s16);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Dup6(s19);
      var s21 := Add(s20);
      assert s21.Peek(2) == 0x8bc;
      var s22 := Push2(s21, 0x0d53);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s23, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 178
    * Starting at 0xd53
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd53 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x8bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8bc;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0d5e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s6, gas - 1)
      else
        ExecuteFromCFGNode_s190(s6, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 179
    * Starting at 0xd5b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x8bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(1) == 0x8bc;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s3, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 110
    * Starting at 0x8bc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8bc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := SStore(s1);
      var s3 := SStore(s2);
      var s4 := Push2(s3, 0x0897);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s5, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 180
    * Starting at 0xd5e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x8bc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8bc;
      var s2 := Push0(s1);
      var s3 := Dup2(s2);
      var s4 := SStore(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0d53);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s8, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 167
    * Starting at 0xca4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x876

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x876;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x22);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0x876;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 194
    * Segment Id for this node is: 168
    * Starting at 0xcb8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x876

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x876;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x7f);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Push2(s5, 0x0c99);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s7, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 111
    * Starting at 0x8c3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

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
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 196
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 197
    * Segment Id for this node is: 111
    * Starting at 0x8c3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 198
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
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

  /** Node 199
    * Segment Id for this node is: 112
    * Starting at 0x8d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x02ad);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s4, gas - 1)
      else
        ExecuteFromCFGNode_s200(s4, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 113
    * Starting at 0x8dd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x08e5);
      assert s1.Peek(0) == 0x8e5;
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x0b52);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s4, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 143
    * Starting at 0xb52
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      var s2 := Push1(s1, 0x40);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x03);
      var s5 := Not(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x02ad);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s9, gas - 1)
      else
        ExecuteFromCFGNode_s202(s9, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 144
    * Starting at 0xb5f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      assert s1.Peek(1) == 0x8e5;
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x8e5;
      var s12 := Push2(s11, 0x02ad);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s13, gas - 1)
      else
        ExecuteFromCFGNode_s203(s13, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 145
    * Starting at 0xb72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0x8e5;
      var s2 := Push1(s1, 0x24);
      var s3 := CallDataLoad(s2);
      var s4 := Push4(s3, 0xffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x02ad);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s10, gas - 1)
      else
        ExecuteFromCFGNode_s204(s10, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 146
    * Starting at 0xb83
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0x8e5;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s2, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 114
    * Starting at 0x8e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Push0(s2);
      var s4 := Push1(s3, 0x80);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push2(s6, 0x08f5);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0c34);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s10, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 158
    * Starting at 0xc34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x8f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8f5;
      var s2 := Push1(s1, 0xa0);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup3(s8);
      var s10 := Gt(s9);
      var s11 := Or(s10);
      assert s11.Peek(2) == 0x8f5;
      var s12 := Push2(s11, 0x02b1);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s13, gas - 1)
      else
        ExecuteFromCFGNode_s207(s13, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 159
    * Starting at 0xc4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x8f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x8f5;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s3, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 115
    * Starting at 0x8f5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup3(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Dup3(s9);
      var s11 := Push1(s10, 0x40);
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := Dup1(s15);
      var s17 := Dup3(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      var s22 := Push1(s21, 0x01);
      var s23 := Dup1(s22);
      var s24 := Push1(s23, 0xa0);
      var s25 := Shl(s24);
      var s26 := Sub(s25);
      var s27 := And(s26);
      var s28 := Push0(s27);
      var s29 := MStore(s28);
      var s30 := Push0(s29);
      var s31 := Push1(s30, 0x20);
      var s32 := MStore(s31);
      var s33 := Push4(s32, 0xffffffff);
      var s34 := Push1(s33, 0x01);
      var s35 := Push1(s34, 0x40);
      var s36 := Push0(s35);
      var s37 := Keccak256(s36);
      var s38 := Add(s37);
      var s39 := Swap2(s38);
      var s40 := And(s39);
      var s41 := Push0(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s209(s41, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 116
    * Starting at 0x92a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MStore(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Push0(s4);
      var s6 := Keccak256(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push2(s8, 0x093d);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x0c34);
      assert s11.Peek(0) == 0xc34;
      assert s11.Peek(2) == 0x93d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s12, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 158
    * Starting at 0xc34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x93d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x93d;
      var s2 := Push1(s1, 0xa0);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup3(s8);
      var s10 := Gt(s9);
      var s11 := Or(s10);
      assert s11.Peek(2) == 0x93d;
      var s12 := Push2(s11, 0x02b1);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s13, gas - 1)
      else
        ExecuteFromCFGNode_s211(s13, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 159
    * Starting at 0xc4c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x93d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x93d;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s3, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 117
    * Starting at 0x93d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := IsZero(s6);
      var s8 := IsZero(s7);
      var s9 := Dup3(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x08);
      var s12 := Shr(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := And(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x01);
      var s26 := Dup4(s25);
      var s27 := Add(s26);
      var s28 := SLoad(s27);
      var s29 := Push1(s28, 0x40);
      var s30 := Dup4(s29);
      var s31 := Add(s30);
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x02);
      var s34 := Dup4(s33);
      var s35 := Add(s34);
      var s36 := Dup1(s35);
      var s37 := SLoad(s36);
      var s38 := Swap4(s37);
      var s39 := Swap1(s38);
      var s40 := Push2(s39, 0x0975);
      var s41 := Dup6(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s213(s41, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 118
    * Starting at 0x971
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x971 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x975

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0c72);
      assert s1.Peek(0) == 0xc72;
      assert s1.Peek(2) == 0x975;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s2, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 162
    * Starting at 0xc72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x975

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x975;
      var s2 := Push8(s1, 0xffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x02b1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s6, gas - 1)
      else
        ExecuteFromCFGNode_s215(s6, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 163
    * Starting at 0xc82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x975

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(2) == 0x975;
      var s2 := Shl(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s6, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 119
    * Starting at 0x975
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x975 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap5(s1);
      var s3 := Push2(s2, 0x0983);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Swap7(s5);
      var s7 := Dup8(s6);
      var s8 := Push2(s7, 0x0c50);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s9, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 160
    * Starting at 0xc50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x983

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x983;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup1(s3);
      var s5 := Not(s4);
      var s6 := Swap2(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x983;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup3(s14);
      var s16 := Gt(s15);
      var s17 := Or(s16);
      var s18 := Push2(s17, 0x02b1);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s19, gas - 1)
      else
        ExecuteFromCFGNode_s218(s19, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 161
    * Starting at 0xc6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x983

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x983;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s3, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 120
    * Starting at 0x983
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Dup7(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      var s9 := Push0(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x20);
      var s12 := Push0(s11);
      var s13 := Keccak256(s12);
      var s14 := Push0(s13);
      var s15 := Swap3(s14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s220(s15, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 121
    * Starting at 0x994
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x994 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0a64);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s235(s6, gas - 1)
      else
        ExecuteFromCFGNode_s221(s6, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 122
    * Starting at 0x99c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x99c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup5(s7);
      var s9 := Add(s8);
      var s10 := Swap5(s9);
      var s11 := Dup6(s10);
      var s12 := MStore(s11);
      var s13 := Add(s12);
      var s14 := SLoad(s13);
      var s15 := Swap3(s14);
      var s16 := Push1(s15, 0x80);
      var s17 := Dup4(s16);
      var s18 := Add(s17);
      var s19 := Swap4(s18);
      var s20 := Dup5(s19);
      var s21 := MStore(s20);
      var s22 := Push1(s21, 0x40);
      var s23 := Dup1(s22);
      var s24 := MLoad(s23);
      var s25 := Swap4(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Dup6(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0xc0);
      var s30 := Dup6(s29);
      var s31 := Add(s30);
      var s32 := Swap4(s31);
      var s33 := Dup2(s32);
      var s34 := MLoad(s33);
      var s35 := IsZero(s34);
      var s36 := IsZero(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Dup8(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := Push1(s40, 0x01);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s222(s41, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 123
    * Starting at 0x9cd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push1(s1, 0xa0);
      var s3 := Shl(s2);
      var s4 := Sub(s3);
      var s5 := Swap1(s4);
      var s6 := MLoad(s5);
      var s7 := And(s6);
      var s8 := Dup3(s7);
      var s9 := Dup7(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      var s12 := Add(s11);
      var s13 := MLoad(s12);
      var s14 := Push1(s13, 0x60);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := MLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0xa0);
      var s21 := Push1(s20, 0x80);
      var s22 := Dup5(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Dup2(s24);
      var s26 := MLoad(s25);
      var s27 := Dup1(s26);
      var s28 := Swap2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0xe0);
      var s31 := Dup4(s30);
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Push1(s33, 0x20);
      var s35 := Push1(s34, 0xe0);
      var s36 := Dup3(s35);
      var s37 := Push1(s36, 0x05);
      var s38 := Shl(s37);
      var s39 := Dup7(s38);
      var s40 := Add(s39);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s223(s41, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 124
    * Starting at 0x9fe
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      var s2 := Add(s1);
      var s3 := Swap2(s2);
      var s4 := Push0(s3);
      var s5 := Swap1(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s224(s5, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 125
    * Starting at 0xa03
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa03 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0a17);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s6, gas - 1)
      else
        ExecuteFromCFGNode_s225(s6, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 126
    * Starting at 0xa0b
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup7(s0);
      var s2 := MLoad(s1);
      var s3 := Push1(s2, 0xa0);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Dup6(s6);
      var s8 := Dup6(s7);
      var s9 := Sub(s8);
      var s10 := Dup7(s9);
      var s11 := Return(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 226
    * Segment Id for this node is: 127
    * Starting at 0xa17
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := Swap3(s3);
      var s5 := Swap4(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup1(s6);
      var s8 := Push2(s7, 0x0a56);
      var s9 := Push1(s8, 0x01);
      var s10 := Swap4(s9);
      var s11 := Push1(s10, 0xdf);
      assert s11.Peek(2) == 0xa56;
      var s12 := Not(s11);
      var s13 := Dup11(s12);
      var s14 := Dup3(s13);
      var s15 := Sub(s14);
      var s16 := Add(s15);
      var s17 := Dup7(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x60);
      var s20 := Push1(s19, 0x40);
      var s21 := Dup11(s20);
      assert s21.Peek(4) == 0xa56;
      var s22 := MLoad(s21);
      var s23 := Dup8(s22);
      var s24 := Dup1(s23);
      var s25 := Push1(s24, 0xa0);
      var s26 := Shl(s25);
      var s27 := Sub(s26);
      var s28 := Dup2(s27);
      var s29 := MLoad(s28);
      var s30 := And(s29);
      var s31 := Dup5(s30);
      assert s31.Peek(6) == 0xa56;
      var s32 := MStore(s31);
      var s33 := Dup6(s32);
      var s34 := Dup2(s33);
      var s35 := Add(s34);
      var s36 := MLoad(s35);
      var s37 := Dup7(s36);
      var s38 := Dup6(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s227(s41, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 128
    * Starting at 0xa48
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := MLoad(s0);
      assert s1.Peek(3) == 0xa56;
      var s2 := Swap2(s1);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0ba6);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s11, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 151
    * Starting at 0xba6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa56;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap2(s3);
      var s5 := Push2(s4, 0x0bbf);
      var s6 := Dup2(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Swap3(s8);
      var s10 := Dup2(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(4) == 0xbbf;
      assert s11.Peek(8) == 0xa56;
      var s12 := MStore(s11);
      var s13 := Dup6(s12);
      var s14 := Dup1(s13);
      var s15 := Dup7(s14);
      var s16 := Add(s15);
      var s17 := Swap2(s16);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0b85);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s20, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 147
    * Starting at 0xb85
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0xbbf

    requires s0.stack[7] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbbf;
      assert s1.Peek(7) == 0xa56;
      var s2 := Push0(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s230(s2, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 148
    * Starting at 0xb87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbbf;
      assert s1.Peek(8) == 0xa56;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0b96);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s6, gas - 1)
      else
        ExecuteFromCFGNode_s231(s6, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 149
    * Starting at 0xb8f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0xbbf;
      assert s1.Peek(7) == 0xa56;
      var s2 := Pop(s1);
      var s3 := Push0(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s7, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 152
    * Starting at 0xbbf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa56;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Add(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s10, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 129
    * Starting at 0xa56
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa56 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap7(s1);
      var s3 := Add(s2);
      var s4 := Swap3(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Push2(s10, 0x0a03);
      assert s11.Peek(0) == 0xa03;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s12, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 150
    * Starting at 0xb96
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb96 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0xbbf

    requires s0.stack[8] == 0xa56

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xbbf;
      assert s1.Peek(8) == 0xa56;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0xbbf;
      assert s11.Peek(8) == 0xa56;
      var s12 := Push2(s11, 0x0b87);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s13, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 130
    * Starting at 0xa64
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Lt(s8);
      var s10 := Push8(s9, 0xffffffffffffffff);
      var s11 := Push1(s10, 0x60);
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := Or(s14);
      var s16 := Push2(s15, 0x02b1);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s256(s17, gas - 1)
      else
        ExecuteFromCFGNode_s236(s17, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 131
    * Starting at 0xa82
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa82 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Push1(s1, 0x03);
      var s3 := Swap2(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap6(s6);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup5(s10);
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Dup7(s15);
      var s17 := SLoad(s16);
      var s18 := And(s17);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Dup5(s20);
      var s22 := Dup7(s21);
      var s23 := Add(s22);
      var s24 := SLoad(s23);
      var s25 := Dup4(s24);
      var s26 := Dup3(s25);
      var s27 := Add(s26);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x40);
      var s30 := MLoad(s29);
      var s31 := Push2(s30, 0x0abe);
      assert s31.Peek(0) == 0xabe;
      var s32 := Dup2(s31);
      var s33 := Push2(s32, 0x0ab7);
      var s34 := Dup2(s33);
      var s35 := Push1(s34, 0x02);
      var s36 := Dup12(s35);
      var s37 := Add(s36);
      var s38 := Push2(s37, 0x0cc2);
      var s39 := Jump(s38);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s39, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 169
    * Starting at 0xcc2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcc2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0xab7

    requires s0.stack[4] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xab7;
      assert s1.Peek(4) == 0xabe;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push0(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Push2(s6, 0x0cd0);
      var s8 := Dup3(s7);
      var s9 := Push2(s8, 0x0c8a);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s10, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 164
    * Starting at 0xc8a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[1] == 0xcd0

    requires s0.stack[5] == 0xab7

    requires s0.stack[8] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd0;
      assert s1.Peek(5) == 0xab7;
      assert s1.Peek(8) == 0xabe;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup3(s3);
      var s5 := Dup2(s4);
      var s6 := Shr(s5);
      var s7 := Swap3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0cb8);
      assert s11.Peek(0) == 0xcb8;
      assert s11.Peek(3) == 0xcd0;
      assert s11.Peek(8) == 0xab7;
      assert s11.Peek(11) == 0xabe;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s12, gas - 1)
      else
        ExecuteFromCFGNode_s239(s12, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 165
    * Starting at 0xc99
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc99 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0xcd0

    requires s0.stack[6] == 0xab7

    requires s0.stack[9] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd0;
      assert s1.Peek(6) == 0xab7;
      assert s1.Peek(9) == 0xabe;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Eq(s4);
      var s6 := Push2(s5, 0x0ca4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s254(s7, gas - 1)
      else
        ExecuteFromCFGNode_s240(s7, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 166
    * Starting at 0xca3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xcd0

    requires s0.stack[5] == 0xab7

    requires s0.stack[8] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s1, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 170
    * Starting at 0xcd0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0xab7

    requires s0.stack[7] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xab7;
      assert s1.Peek(7) == 0xabe;
      var s2 := Swap2(s1);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap4(s6);
      var s8 := Push1(s7, 0x01);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0xab7;
      assert s11.Peek(11) == 0xabe;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push0(s14);
      var s16 := Eq(s15);
      var s17 := Push2(s16, 0x0d34);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s18, gas - 1)
      else
        ExecuteFromCFGNode_s242(s18, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 171
    * Starting at 0xce7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xce7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[7] == 0xab7

    requires s0.stack[10] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0xab7;
      assert s1.Peek(9) == 0xabe;
      var s2 := Push1(s1, 0x01);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0cf6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s249(s5, gas - 1)
      else
        ExecuteFromCFGNode_s243(s5, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 172
    * Starting at 0xcef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xab7

    requires s0.stack[8] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xab7;
      assert s1.Peek(8) == 0xabe;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s7, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 132
    * Starting at 0xab7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xabe;
      var s2 := Sub(s1);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0c50);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s5, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 160
    * Starting at 0xc50
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc50 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xabe;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Dup1(s3);
      var s5 := Not(s4);
      var s6 := Swap2(s5);
      var s7 := Add(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xabe;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push8(s13, 0xffffffffffffffff);
      var s15 := Dup3(s14);
      var s16 := Gt(s15);
      var s17 := Or(s16);
      var s18 := Push2(s17, 0x02b1);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s19, gas - 1)
      else
        ExecuteFromCFGNode_s246(s19, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 161
    * Starting at 0xc6e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xabe;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s247(s3, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 133
    * Starting at 0xabe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xabe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Add(s7);
      var s9 := Swap3(s8);
      var s10 := Add(s9);
      var s11 := Swap4(s10);
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x0994);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s16, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xabe;
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
      assert s11.Peek(3) == 0xabe;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 249
    * Segment Id for this node is: 173
    * Starting at 0xcf6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[5] == 0xab7

    requires s0.stack[8] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xab7;
      assert s1.Peek(8) == 0xabe;
      var s2 := Swap1(s1);
      var s3 := Swap4(s2);
      var s4 := Swap5(s3);
      var s5 := Swap6(s4);
      var s6 := Pop(s5);
      var s7 := Push0(s6);
      var s8 := Swap3(s7);
      var s9 := Swap2(s8);
      var s10 := Swap3(s9);
      var s11 := MStore(s10);
      assert s11.Peek(4) == 0xab7;
      assert s11.Peek(6) == 0xabe;
      var s12 := Dup4(s11);
      var s13 := Push0(s12);
      var s14 := Keccak256(s13);
      var s15 := Swap3(s14);
      var s16 := Dup5(s15);
      var s17 := Push0(s16);
      var s18 := Swap5(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s250(s18, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 174
    * Starting at 0xd08
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[7] == 0xab7

    requires s0.stack[9] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xab7;
      assert s1.Peek(9) == 0xabe;
      var s2 := Dup4(s1);
      var s3 := Dup7(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0d20);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s6, gas - 1)
      else
        ExecuteFromCFGNode_s251(s6, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 175
    * Starting at 0xd10
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd10 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[7] == 0xab7

    requires s0.stack[9] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(6) == 0xab7;
      assert s1.Peek(8) == 0xabe;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Push0(s7);
      var s9 := Dup1(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0xab7;
      assert s11.Peek(7) == 0xabe;
      var s12 := Dup1(s11);
      var s13 := Push2(s12, 0x0cef);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s14, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 176
    * Starting at 0xd20
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd20 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[7] == 0xab7

    requires s0.stack[9] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xab7;
      assert s1.Peek(9) == 0xabe;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Dup6(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Swap5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0xab7;
      assert s11.Peek(8) == 0xabe;
      var s12 := Swap4(s11);
      var s13 := Dup6(s12);
      var s14 := Swap1(s13);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x0d08);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s18, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 177
    * Starting at 0xd34
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[7] == 0xab7

    requires s0.stack[10] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0xab7;
      assert s1.Peek(10) == 0xabe;
      var s2 := Push1(s1, 0xff);
      var s3 := Not(s2);
      var s4 := And(s3);
      var s5 := Dup7(s4);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0xab7;
      assert s11.Peek(6) == 0xabe;
      var s12 := Swap1(s11);
      var s13 := IsZero(s12);
      var s14 := IsZero(s13);
      var s15 := Push1(s14, 0x05);
      var s16 := Shl(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := Swap2(s18);
      var s20 := Pop(s19);
      var s21 := Push0(s20);
      assert s21.Peek(1) == 0xab7;
      assert s21.Peek(4) == 0xabe;
      var s22 := Dup1(s21);
      var s23 := Dup1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup1(s24);
      var s26 := Push2(s25, 0x0cef);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s27, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 167
    * Starting at 0xca4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xca4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0xcd0

    requires s0.stack[5] == 0xab7

    requires s0.stack[8] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xcd0;
      assert s1.Peek(5) == 0xab7;
      assert s1.Peek(8) == 0xabe;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push0(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x22);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push0(s10);
      assert s11.Peek(2) == 0xcd0;
      assert s11.Peek(7) == 0xab7;
      assert s11.Peek(10) == 0xabe;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 255
    * Segment Id for this node is: 168
    * Starting at 0xcb8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[1] == 0xcd0

    requires s0.stack[6] == 0xab7

    requires s0.stack[9] == 0xabe

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xcd0;
      assert s1.Peek(6) == 0xab7;
      assert s1.Peek(9) == 0xabe;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x7f);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Push2(s5, 0x0c99);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s7, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

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
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 257
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x983

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x983;
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
      assert s11.Peek(3) == 0x983;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 258
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x975

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x975;
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
      assert s11.Peek(3) == 0x975;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 259
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x93d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x93d;
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
      assert s11.Peek(3) == 0x93d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 260
    * Segment Id for this node is: 39
    * Starting at 0x2b1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x8f5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8f5;
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
      assert s11.Peek(3) == 0x8f5;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 261
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 262
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8e5;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 263
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x8e5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x8e5;
      var s2 := Push0(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 264
    * Segment Id for this node is: 134
    * Starting at 0xad1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x02ad);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s4, gas - 1)
      else
        ExecuteFromCFGNode_s265(s4, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 135
    * Starting at 0xad7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push0(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x02ad);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s8, gas - 1)
      else
        ExecuteFromCFGNode_s266(s8, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 136
    * Starting at 0xae2
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push20(s3, 0x2309762aaca0a8f689463a42c0a6a84be3a7ea51);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 267
    * Segment Id for this node is: 137
    * Starting at 0xaff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x02ad);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s4, gas - 1)
      else
        ExecuteFromCFGNode_s268(s4, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 138
    * Starting at 0xb05
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb05 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x03);
      var s4 := Not(s3);
      var s5 := Add(s4);
      var s6 := SLt(s5);
      var s7 := Push2(s6, 0x02ad);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s8, gas - 1)
      else
        ExecuteFromCFGNode_s269(s8, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 139
    * Starting at 0xb11
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb11 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0xffffffff);
      var s5 := Push1(s4, 0xe0);
      var s6 := Shl(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Swap3(s9);
      var s11 := Sub(s10);
      var s12 := Push2(s11, 0x02ad);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s273(s13, gas - 1)
      else
        ExecuteFromCFGNode_s270(s13, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 140
    * Starting at 0xb26
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb26 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Swap2(s1);
      var s3 := Push4(s2, 0xcb7d736d);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := Eq(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0b41);
      assert s11.Peek(0) == 0xb41;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s272(s12, gas - 1)
      else
        ExecuteFromCFGNode_s271(s12, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 141
    * Starting at 0xb3a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 272
    * Segment Id for this node is: 142
    * Starting at 0xb41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x01ffc9a7);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Eq(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup4(s7);
      var s9 := Push2(s8, 0x0b3a);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s10, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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

  /** Node 274
    * Segment Id for this node is: 38
    * Starting at 0x2ad
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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
