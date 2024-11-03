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
      var s6 := Push2(s5, 0x0078);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s387(s7, gas - 1)
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
      var s6 := Push4(s5, 0x248a9ca3);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x007d);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s378(s9, gas - 1)
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
      var s2 := Push4(s1, 0x2f2ff15d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00a3);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8bb9c5bf);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00b8);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s225(s5, gas - 1)
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
      var s2 := Push4(s1, 0x9010d07c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00cb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s205(s5, gas - 1)
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
      var s2 := Push4(s1, 0x91d14854);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00f6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s5, gas - 1)
      else
        ExecuteFromCFGNode_s8(s5, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xca15c873);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0119);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xd547741f);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x012c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 10
    * Starting at 0x6d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xe1c7392a);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x013f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s5, gas - 1)
      else
        ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 11
    * Starting at 0x78
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
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

  /** Node 12
    * Segment Id for this node is: 31
    * Starting at 0x13f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b6);
      var s3 := Push2(s2, 0x01cb);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s4, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 47
    * Starting at 0x1cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb6;
      var s2 := Push2(s1, 0x01d6);
      var s3 := Push1(s2, 0x00);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x022a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s6, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 53
    * Starting at 0x22a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1d6

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1d6;
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x024b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0236);
      var s5 := Push2(s4, 0x0357);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s6, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x236

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x1d6

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x236;
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x1d6;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s4, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 54
    * Starting at 0x236
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x1d6

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x1d6;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x24b;
      assert s11.Peek(6) == 0x1d6;
      assert s11.Peek(7) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x03ea);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s16, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 75
    * Starting at 0x3ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x1d6

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x1d6;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x24b;
      assert s11.Peek(9) == 0x1d6;
      assert s11.Peek(10) == 0xb6;
      var s12 := Push2(s11, 0x05a3);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s13, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 100
    * Starting at 0x5a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x24b

    requires s0.stack[9] == 0x1d6

    requires s0.stack[10] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(9) == 0x1d6;
      assert s1.Peek(10) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05af);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x062d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s7, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 108
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x5af

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x24b

    requires s0.stack[13] == 0x1d6

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5af;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x24b;
      assert s1.Peek(13) == 0x1d6;
      assert s1.Peek(14) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x5af;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x24b;
      assert s11.Peek(14) == 0x1d6;
      assert s11.Peek(15) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s20, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 101
    * Starting at 0x5af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x24b

    requires s0.stack[11] == 0x1d6

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x24b;
      assert s1.Peek(11) == 0x1d6;
      assert s1.Peek(12) == 0xb6;
      var s2 := Push2(s1, 0x0152);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s3, gas - 1)
      else
        ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 102
    * Starting at 0x5b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x24b

    requires s0.stack[10] == 0x1d6

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(9) == 0x1d6;
      assert s1.Peek(10) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Dup5(s7);
      var s9 := SStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0x191;
      assert s11.Peek(10) == 0x24b;
      assert s11.Peek(13) == 0x1d6;
      assert s11.Peek(14) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Keccak256(s16);
      var s18 := Swap1(s17);
      var s19 := Swap4(s18);
      var s20 := Add(s19);
      var s21 := Dup5(s20);
      assert s21.Peek(7) == 0x191;
      assert s21.Peek(11) == 0x24b;
      assert s21.Peek(14) == 0x1d6;
      assert s21.Peek(15) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := SStore(s22);
      var s24 := Dup5(s23);
      var s25 := SLoad(s24);
      var s26 := Swap4(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Swap4(s28);
      var s30 := Dup2(s29);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x191;
      assert s31.Peek(9) == 0x24b;
      assert s31.Peek(12) == 0x1d6;
      assert s31.Peek(13) == 0xb6;
      var s32 := Swap1(s31);
      var s33 := Swap2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := Swap1(s35);
      var s37 := Swap3(s36);
      var s38 := Keccak256(s37);
      var s39 := SStore(s38);
      var s40 := Swap1(s39);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s41, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x24b

    requires s0.stack[7] == 0x1d6

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x24b;
      assert s1.Peek(7) == 0x1d6;
      assert s1.Peek(8) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s7, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 55
    * Starting at 0x24b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1d6

    requires s0.stack[4] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1d6;
      assert s1.Peek(4) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x1d6;
      assert s11.Peek(6) == 0xb6;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Dup5(s14);
      var s16 := Swap1(s15);
      var s17 := Push32(s16, 0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Swap1(s19);
      var s21 := Log4(s20);
      assert s21.Peek(2) == 0x1d6;
      assert s21.Peek(3) == 0xb6;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s24, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 48
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb6;
      var s2 := Push2(s1, 0x0200);
      var s3 := Push32(s2, 0xab538675bf961a344c31ab0f84b867b850736e871cc7bf3055ce65100abe02ea);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x022a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s6, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 53
    * Starting at 0x22a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x200

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x200;
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x024b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0236);
      var s5 := Push2(s4, 0x0357);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x236

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x200

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x236;
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x200;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s4, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 54
    * Starting at 0x236
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x200

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x200;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x24b;
      assert s11.Peek(6) == 0x200;
      assert s11.Peek(7) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x03ea);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s16, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 75
    * Starting at 0x3ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x200

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x200;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x24b;
      assert s11.Peek(9) == 0x200;
      assert s11.Peek(10) == 0xb6;
      var s12 := Push2(s11, 0x05a3);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s13, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 100
    * Starting at 0x5a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x24b

    requires s0.stack[9] == 0x200

    requires s0.stack[10] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(9) == 0x200;
      assert s1.Peek(10) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05af);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x062d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s7, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 108
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x5af

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x24b

    requires s0.stack[13] == 0x200

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5af;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x24b;
      assert s1.Peek(13) == 0x200;
      assert s1.Peek(14) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x5af;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x24b;
      assert s11.Peek(14) == 0x200;
      assert s11.Peek(15) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s20, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 101
    * Starting at 0x5af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x24b

    requires s0.stack[11] == 0x200

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x24b;
      assert s1.Peek(11) == 0x200;
      assert s1.Peek(12) == 0xb6;
      var s2 := Push2(s1, 0x0152);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s3, gas - 1)
      else
        ExecuteFromCFGNode_s32(s3, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 102
    * Starting at 0x5b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x24b

    requires s0.stack[10] == 0x200

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(9) == 0x200;
      assert s1.Peek(10) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Dup5(s7);
      var s9 := SStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0x191;
      assert s11.Peek(10) == 0x24b;
      assert s11.Peek(13) == 0x200;
      assert s11.Peek(14) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Keccak256(s16);
      var s18 := Swap1(s17);
      var s19 := Swap4(s18);
      var s20 := Add(s19);
      var s21 := Dup5(s20);
      assert s21.Peek(7) == 0x191;
      assert s21.Peek(11) == 0x24b;
      assert s21.Peek(14) == 0x200;
      assert s21.Peek(15) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := SStore(s22);
      var s24 := Dup5(s23);
      var s25 := SLoad(s24);
      var s26 := Swap4(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Swap4(s28);
      var s30 := Dup2(s29);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x191;
      assert s31.Peek(9) == 0x24b;
      assert s31.Peek(12) == 0x200;
      assert s31.Peek(13) == 0xb6;
      var s32 := Swap1(s31);
      var s33 := Swap2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := Swap1(s35);
      var s37 := Swap3(s36);
      var s38 := Keccak256(s37);
      var s39 := SStore(s38);
      var s40 := Swap1(s39);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s41, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x24b

    requires s0.stack[7] == 0x200

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x24b;
      assert s1.Peek(7) == 0x200;
      assert s1.Peek(8) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s7, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 55
    * Starting at 0x24b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x200

    requires s0.stack[4] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x200;
      assert s1.Peek(4) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x200;
      assert s11.Peek(6) == 0xb6;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Dup5(s14);
      var s16 := Swap1(s15);
      var s17 := Push32(s16, 0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Swap1(s19);
      var s21 := Log4(s20);
      assert s21.Peek(2) == 0x200;
      assert s21.Peek(3) == 0xb6;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s24, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 49
    * Starting at 0x200
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x200 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xb6;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s2, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 18
    * Starting at 0xb6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb6 as nat
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

  /** Node 37
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x24b

    requires s0.stack[10] == 0x200

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x191;
      assert s1.Peek(7) == 0x24b;
      assert s1.Peek(10) == 0x200;
      assert s1.Peek(11) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s6, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x24b

    requires s0.stack[10] == 0x1d6

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x191;
      assert s1.Peek(7) == 0x24b;
      assert s1.Peek(10) == 0x1d6;
      assert s1.Peek(11) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s6, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 29
    * Starting at 0x12c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b6);
      var s3 := Push2(s2, 0x013a);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0723);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 121
    * Starting at 0x723
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x13a

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13a;
      assert s1.Peek(3) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0736);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s11, gas - 1)
      else
        ExecuteFromCFGNode_s41(s11, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 122
    * Starting at 0x732
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x732 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x13a

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x13a;
      assert s1.Peek(6) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 42
    * Segment Id for this node is: 123
    * Starting at 0x736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x13a

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x13a;
      assert s1.Peek(5) == 0xb6;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x13a;
      assert s11.Peek(8) == 0xb6;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := Dup2(s14);
      var s16 := And(s15);
      var s17 := Dup2(s16);
      var s18 := Eq(s17);
      var s19 := Push2(s18, 0x0754);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s20, gas - 1)
      else
        ExecuteFromCFGNode_s43(s20, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 124
    * Starting at 0x750
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x750 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x13a

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x13a;
      assert s1.Peek(7) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 44
    * Segment Id for this node is: 125
    * Starting at 0x754
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x754 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x13a

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x13a;
      assert s1.Peek(6) == 0xb6;
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
      ExecuteFromCFGNode_s45(s11, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 30
    * Starting at 0x13a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb6;
      var s2 := Push2(s1, 0x01af);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s3, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 44
    * Starting at 0x1af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb6;
      var s2 := Push2(s1, 0x01b8);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0202);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s5, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 50
    * Starting at 0x202
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x1b8

    requires s0.stack[4] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b8;
      assert s1.Peek(4) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x020c);
      var s4 := Push2(s3, 0x0357);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s5, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x20c

    requires s0.stack[3] == 0x1b8

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x20c;
      assert s1.Peek(3) == 0x1b8;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s4, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 51
    * Starting at 0x20c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x1b8

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b8;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap3(s2);
      var s4 := Dup4(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x1b8;
      assert s11.Peek(4) == 0xb6;
      var s12 := Push1(s11, 0x02);
      var s13 := Add(s12);
      var s14 := SLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s16, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 45
    * Starting at 0x1b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x01c1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0220);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s5, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 52
    * Starting at 0x220
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x220 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x1c1

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c1;
      assert s1.Peek(5) == 0xb6;
      var s2 := Push2(s1, 0x0182);
      var s3 := Dup2(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x037b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 67
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x1c1

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x182;
      assert s1.Peek(4) == 0x1c1;
      assert s1.Peek(8) == 0xb6;
      var s2 := Push2(s1, 0x0385);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02b5);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s6, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 59
    * Starting at 0x2b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x385

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x1c1

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x385;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x1c1;
      assert s1.Peek(11) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c3);
      var s6 := Push2(s5, 0x0357);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s7, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x2c3

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x385

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2c3;
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x385;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s4, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 60
    * Starting at 0x2c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x385

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x385;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup7(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x385;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x1c1;
      assert s11.Peek(16) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x040b);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s16, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 77
    * Starting at 0x40b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x385

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x385;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x191;
      assert s11.Peek(10) == 0x385;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x1c1;
      assert s11.Peek(19) == 0xb6;
      var s12 := Push2(s11, 0x062d);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s13, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 108
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x385

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x385;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x385;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s20, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x385

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x385;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s7, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x385

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0x1c1

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x385;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0x1c1;
      assert s1.Peek(13) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s7, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 68
    * Starting at 0x385
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x1c1

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push2(s1, 0x03e6);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s3, gas - 1)
      else
        ExecuteFromCFGNode_s61(s3, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 69
    * Starting at 0x38a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x1c1

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x039b);
      assert s1.Peek(0) == 0x39b;
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(9) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x043f);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s10, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 80
    * Starting at 0x43f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x39b

    requires s0.stack[4] == 0x182

    requires s0.stack[6] == 0x1c1

    requires s0.stack[10] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x39b;
      assert s1.Peek(4) == 0x182;
      assert s1.Peek(6) == 0x1c1;
      assert s1.Peek(10) == 0xb6;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0152);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s63(s11, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 81
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x152

    requires s0.stack[5] == 0x39b

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x1c1

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x152;
      assert s1.Peek(5) == 0x39b;
      assert s1.Peek(8) == 0x182;
      assert s1.Peek(10) == 0x1c1;
      assert s1.Peek(14) == 0xb6;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0460);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push2(s6, 0x085d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s8, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 139
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x460

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x460;
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
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
      assert s11.Peek(5) == 0x460;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x1c1;
      assert s11.Peek(22) == 0xb6;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0152);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s14, gas - 1)
      else
        ExecuteFromCFGNode_s65(s14, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 140
    * Starting at 0x86d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s3, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x460

    requires s0.stack[9] == 0x152

    requires s0.stack[12] == 0x39b

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x1c1

    requires s0.stack[21] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x460;
      assert s11.Peek(11) == 0x152;
      assert s11.Peek(14) == 0x39b;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x1c1;
      assert s11.Peek(23) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 67
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x460;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s6, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 82
    * Starting at 0x460
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push2(s1, 0x046b);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Push2(s4, 0x0874);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s6, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 141
    * Starting at 0x874
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x874 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x46b

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x46b;
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0152);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s10, gas - 1)
      else
        ExecuteFromCFGNode_s70(s10, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 142
    * Starting at 0x880
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x880 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s3, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x46b

    requires s0.stack[9] == 0x152

    requires s0.stack[12] == 0x39b

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x1c1

    requires s0.stack[21] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x46b;
      assert s11.Peek(11) == 0x152;
      assert s11.Peek(14) == 0x39b;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x1c1;
      assert s11.Peek(23) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 72
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x46b;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s6, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 83
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x40);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0482);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s11, gas - 1)
      else
        ExecuteFromCFGNode_s74(s11, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 84
    * Starting at 0x47b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0482);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x0887);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s3, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 143
    * Starting at 0x887
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x887 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x482

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x39b

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x482;
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 76
    * Segment Id for this node is: 85
    * Starting at 0x482
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x152;
      assert s21.Peek(10) == 0x39b;
      assert s21.Peek(13) == 0x182;
      assert s21.Peek(15) == 0x1c1;
      assert s21.Peek(19) == 0xb6;
      var s22 := Push2(s21, 0x04ac);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s23, gas - 1)
      else
        ExecuteFromCFGNode_s77(s23, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 86
    * Starting at 0x4a0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x39b

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Dup4(s6);
      var s8 := CallDataCopy(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s78(s11, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 87
    * Starting at 0x4ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x39b

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push1(s5, 0xfc);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x04c7);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s15, gas - 1)
      else
        ExecuteFromCFGNode_s79(s15, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 88
    * Starting at 0x4c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04c7);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s3, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4c7

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4c7;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x1c1;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 81
    * Segment Id for this node is: 89
    * Starting at 0x4c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
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
      assert s11.Peek(7) == 0x152;
      assert s11.Peek(10) == 0x39b;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x1c1;
      assert s11.Peek(19) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x0f);
      var s21 := Push1(s20, 0xfb);
      assert s21.Peek(6) == 0x152;
      assert s21.Peek(9) == 0x39b;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x1c1;
      assert s21.Peek(18) == 0xb6;
      var s22 := Shl(s21);
      var s23 := Dup2(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Dup2(s24);
      var s26 := MLoad(s25);
      var s27 := Dup2(s26);
      var s28 := Lt(s27);
      var s29 := Push2(s28, 0x04f6);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s30, gas - 1)
      else
        ExecuteFromCFGNode_s82(s30, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 90
    * Starting at 0x4ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f6);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s3, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4f6

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f6;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x1c1;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 84
    * Segment Id for this node is: 91
    * Starting at 0x4f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
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
      assert s11.Peek(7) == 0x152;
      assert s11.Peek(10) == 0x39b;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x1c1;
      assert s11.Peek(19) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(6) == 0x152;
      assert s21.Peek(9) == 0x39b;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x1c1;
      assert s21.Peek(18) == 0xb6;
      var s22 := Dup5(s21);
      var s23 := Mul(s22);
      var s24 := Add(s23);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s85(s24, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 92
    * Starting at 0x515
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x515 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0583);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s7, gas - 1)
      else
        ExecuteFromCFGNode_s86(s7, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 93
    * Starting at 0x51f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 16, 0x181899199a1a9b1b9c1cb0b131b232b3);
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push1(s1, 0x81);
      var s3 := Shl(s2);
      var s4 := Dup6(s3);
      var s5 := Push1(s4, 0x0f);
      var s6 := And(s5);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x0546);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s11, gas - 1)
      else
        ExecuteFromCFGNode_s87(s11, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 94
    * Starting at 0x53f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0546);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s3, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x546

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x546;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x1c1;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 89
    * Segment Id for this node is: 95
    * Starting at 0x546
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x546 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Byte(s1);
      var s3 := Push1(s2, 0xf8);
      var s4 := Shl(s3);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Dup2(s6);
      var s8 := MLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Lt(s9);
      var s11 := Push2(s10, 0x055c);
      assert s11.Peek(0) == 0x55c;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x1c1;
      assert s11.Peek(22) == 0xb6;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s12, gas - 1)
      else
        ExecuteFromCFGNode_s90(s12, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 96
    * Starting at 0x555
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x555 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x055c);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s3, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x55c

    requires s0.stack[9] == 0x152

    requires s0.stack[12] == 0x39b

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x1c1

    requires s0.stack[21] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x55c;
      assert s11.Peek(11) == 0x152;
      assert s11.Peek(14) == 0x39b;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x1c1;
      assert s11.Peek(23) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 92
    * Segment Id for this node is: 97
    * Starting at 0x55c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
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
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x04);
      var s21 := Swap5(s20);
      assert s21.Peek(6) == 0x152;
      assert s21.Peek(9) == 0x39b;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x1c1;
      assert s21.Peek(18) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := Swap5(s22);
      var s24 := Shr(s23);
      var s25 := Swap4(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Not(s26);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0515);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s30, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 98
    * Starting at 0x583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0191);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s6, gas - 1)
      else
        ExecuteFromCFGNode_s94(s6, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 99
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x39b

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x1c1

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xc9134785);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(6) == 0x152;
      assert s11.Peek(9) == 0x39b;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x1c1;
      assert s11.Peek(18) == 0xb6;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 95
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x39b

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x1c1

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(7) == 0x39b;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x1c1;
      assert s1.Peek(16) == 0xb6;
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
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x39b

    requires s0.stack[6] == 0x182

    requires s0.stack[8] == 0x1c1

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x39b;
      assert s1.Peek(6) == 0x182;
      assert s1.Peek(8) == 0x1c1;
      assert s1.Peek(12) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s6, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 70
    * Starting at 0x39b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x1c1

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push2(s1, 0x03a6);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push2(s4, 0x0451);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 81
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x3a6

    requires s0.stack[6] == 0x182

    requires s0.stack[8] == 0x1c1

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3a6;
      assert s1.Peek(6) == 0x182;
      assert s1.Peek(8) == 0x1c1;
      assert s1.Peek(12) == 0xb6;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0460);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push2(s6, 0x085d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s8, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 139
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x460

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x460;
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
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
      assert s11.Peek(5) == 0x460;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0152);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s14, gas - 1)
      else
        ExecuteFromCFGNode_s100(s14, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 140
    * Starting at 0x86d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s3, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x460

    requires s0.stack[9] == 0x3a6

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x460;
      assert s11.Peek(11) == 0x3a6;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x1c1;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 102
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x460;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 82
    * Starting at 0x460
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push2(s1, 0x046b);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Push2(s4, 0x0874);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 141
    * Starting at 0x874
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x874 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x46b

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x46b;
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0152);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s10, gas - 1)
      else
        ExecuteFromCFGNode_s105(s10, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 142
    * Starting at 0x880
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x880 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x46b

    requires s0.stack[9] == 0x3a6

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x46b;
      assert s11.Peek(11) == 0x3a6;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x1c1;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 107
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x46b;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s6, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 83
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x40);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0482);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s11, gas - 1)
      else
        ExecuteFromCFGNode_s109(s11, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 84
    * Starting at 0x47b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0482);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x1c1;
      assert s1.Peek(16) == 0xb6;
      var s2 := Push2(s1, 0x0887);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s3, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 143
    * Starting at 0x887
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x887 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x482

    requires s0.stack[6] == 0x3a6

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x1c1

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x1c1;
      assert s1.Peek(16) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x482;
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x1c1;
      assert s11.Peek(18) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 111
    * Segment Id for this node is: 85
    * Starting at 0x482
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x1c1;
      assert s11.Peek(18) == 0xb6;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x3a6;
      assert s21.Peek(11) == 0x182;
      assert s21.Peek(13) == 0x1c1;
      assert s21.Peek(17) == 0xb6;
      var s22 := Push2(s21, 0x04ac);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s23, gas - 1)
      else
        ExecuteFromCFGNode_s112(s23, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 86
    * Starting at 0x4a0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x3a6

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x1c1

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Dup4(s6);
      var s8 := CallDataCopy(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s113(s11, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 87
    * Starting at 0x4ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x3a6

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x1c1

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x1c1;
      assert s1.Peek(16) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push1(s5, 0xfc);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x1c1;
      assert s11.Peek(18) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x04c7);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s15, gas - 1)
      else
        ExecuteFromCFGNode_s114(s15, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 88
    * Starting at 0x4c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04c7);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s3, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x4c7

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4c7;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 116
    * Segment Id for this node is: 89
    * Starting at 0x4c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
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
      assert s11.Peek(7) == 0x3a6;
      assert s11.Peek(11) == 0x182;
      assert s11.Peek(13) == 0x1c1;
      assert s11.Peek(17) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x0f);
      var s21 := Push1(s20, 0xfb);
      assert s21.Peek(6) == 0x3a6;
      assert s21.Peek(10) == 0x182;
      assert s21.Peek(12) == 0x1c1;
      assert s21.Peek(16) == 0xb6;
      var s22 := Shl(s21);
      var s23 := Dup2(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Dup2(s24);
      var s26 := MLoad(s25);
      var s27 := Dup2(s26);
      var s28 := Lt(s27);
      var s29 := Push2(s28, 0x04f6);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s30, gas - 1)
      else
        ExecuteFromCFGNode_s117(s30, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 90
    * Starting at 0x4ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f6);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s3, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x4f6

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f6;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 119
    * Segment Id for this node is: 91
    * Starting at 0x4f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
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
      assert s11.Peek(7) == 0x3a6;
      assert s11.Peek(11) == 0x182;
      assert s11.Peek(13) == 0x1c1;
      assert s11.Peek(17) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(6) == 0x3a6;
      assert s21.Peek(10) == 0x182;
      assert s21.Peek(12) == 0x1c1;
      assert s21.Peek(16) == 0xb6;
      var s22 := Dup5(s21);
      var s23 := Mul(s22);
      var s24 := Add(s23);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s24, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 92
    * Starting at 0x515
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x515 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0583);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s7, gas - 1)
      else
        ExecuteFromCFGNode_s121(s7, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 93
    * Starting at 0x51f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 16, 0x181899199a1a9b1b9c1cb0b131b232b3);
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x1c1;
      assert s1.Peek(16) == 0xb6;
      var s2 := Push1(s1, 0x81);
      var s3 := Shl(s2);
      var s4 := Dup6(s3);
      var s5 := Push1(s4, 0x0f);
      var s6 := And(s5);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x0546);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s11, gas - 1)
      else
        ExecuteFromCFGNode_s122(s11, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 94
    * Starting at 0x53f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0546);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x546

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x546;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 124
    * Segment Id for this node is: 95
    * Starting at 0x546
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x546 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Byte(s1);
      var s3 := Push1(s2, 0xf8);
      var s4 := Shl(s3);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Dup2(s6);
      var s8 := MLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Lt(s9);
      var s11 := Push2(s10, 0x055c);
      assert s11.Peek(0) == 0x55c;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s12, gas - 1)
      else
        ExecuteFromCFGNode_s125(s12, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 96
    * Starting at 0x555
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x555 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x055c);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s3, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x55c

    requires s0.stack[9] == 0x3a6

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x55c;
      assert s11.Peek(11) == 0x3a6;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x1c1;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 127
    * Segment Id for this node is: 97
    * Starting at 0x55c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
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
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x1c1;
      assert s11.Peek(18) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x04);
      var s21 := Swap5(s20);
      assert s21.Peek(6) == 0x3a6;
      assert s21.Peek(10) == 0x182;
      assert s21.Peek(12) == 0x1c1;
      assert s21.Peek(16) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := Swap5(s22);
      var s24 := Shr(s23);
      var s25 := Swap4(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Not(s26);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0515);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s30, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 98
    * Starting at 0x583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0191);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s6, gas - 1)
      else
        ExecuteFromCFGNode_s129(s6, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 99
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x3a6

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x1c1

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xc9134785);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(6) == 0x3a6;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x1c1;
      assert s11.Peek(16) == 0xb6;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 130
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x3a6

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x1c1

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3a6;
      assert s1.Peek(8) == 0x182;
      assert s1.Peek(10) == 0x1c1;
      assert s1.Peek(14) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 71
    * Starting at 0x3a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x182

    requires s0.stack[6] == 0x1c1

    requires s0.stack[10] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x182;
      assert s1.Peek(6) == 0x1c1;
      assert s1.Peek(10) == 0xb6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x03b7);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x07a5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s11, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 133
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x3b7

    requires s0.stack[6] == 0x182

    requires s0.stack[8] == 0x1c1

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b7;
      assert s1.Peek(6) == 0x182;
      assert s1.Peek(8) == 0x1c1;
      assert s1.Peek(12) == 0xb6;
      var s2 := PushN(s1, 23, 0x020b1b1b2b9b9a1b7b73a3937b61d1030b1b1b7bab73a1);
      var s3 := Push1(s2, 0x4d);
      var s4 := Shl(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x00);
      var s8 := Dup4(s7);
      var s9 := MLoad(s8);
      var s10 := Push2(s9, 0x07d7);
      var s11 := Dup2(s10);
      assert s11.Peek(1) == 0x7d7;
      assert s11.Peek(7) == 0x3b7;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x1c1;
      assert s11.Peek(16) == 0xb6;
      var s12 := Push1(s11, 0x17);
      var s13 := Dup6(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := Push2(s17, 0x0781);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s19, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 129
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x7d7

    requires s0.stack[9] == 0x3b7

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7d7;
      assert s1.Peek(9) == 0x3b7;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s134(s2, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 130
    * Starting at 0x784
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x7d7

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s136(s7, gas - 1)
      else
        ExecuteFromCFGNode_s135(s7, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 131
    * Starting at 0x78d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x7d7

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x7d7;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0784);
      assert s11.Peek(0) == 0x784;
      assert s11.Peek(5) == 0x7d7;
      assert s11.Peek(11) == 0x3b7;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x1c1;
      assert s11.Peek(20) == 0xb6;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s12, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 132
    * Starting at 0x79c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x7d7

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s8, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 134
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x3b7

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x1c1

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3b7;
      assert s1.Peek(8) == 0x182;
      assert s1.Peek(10) == 0x1c1;
      assert s1.Peek(14) == 0xb6;
      var s2 := PushN(s1, 17, 0x01034b99036b4b9b9b4b733903937b6329);
      var s3 := Push1(s2, 0x7d);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x17);
      var s6 := Swap2(s5);
      var s7 := Dup5(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x3b7;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x1c1;
      assert s11.Peek(16) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Dup4(s12);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0808);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x28);
      var s18 := Dup5(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup9(s20);
      assert s21.Peek(4) == 0x808;
      assert s21.Peek(11) == 0x3b7;
      assert s21.Peek(14) == 0x182;
      assert s21.Peek(16) == 0x1c1;
      assert s21.Peek(20) == 0xb6;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0781);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s24, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 129
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x808

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x1c1

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x808;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s139(s2, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 130
    * Starting at 0x784
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x808

    requires s0.stack[11] == 0x3b7

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x808;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s7, gas - 1)
      else
        ExecuteFromCFGNode_s140(s7, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 131
    * Starting at 0x78d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x808

    requires s0.stack[11] == 0x3b7

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x808;
      assert s1.Peek(12) == 0x3b7;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x1c1;
      assert s1.Peek(21) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0784);
      assert s11.Peek(0) == 0x784;
      assert s11.Peek(5) == 0x808;
      assert s11.Peek(12) == 0x3b7;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x1c1;
      assert s11.Peek(21) == 0xb6;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s12, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 132
    * Starting at 0x79c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x808

    requires s0.stack[11] == 0x3b7

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x1c1

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x808;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x1c1;
      assert s1.Peek(20) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s8, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 135
    * Starting at 0x808
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x808 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x3b7

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x1c1

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3b7;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x1c1;
      assert s1.Peek(15) == 0xb6;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x28);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Swap4(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s11, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 72
    * Starting at 0x3b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x1c1

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(9) == 0xb6;
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
      assert s11.Peek(7) == 0x182;
      assert s11.Peek(9) == 0x1c1;
      assert s11.Peek(13) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Swap1(s12);
      var s14 := Dup3(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push3(s16, 0x461bcd);
      var s18 := Push1(s17, 0xe5);
      var s19 := Shl(s18);
      var s20 := Dup3(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0x182;
      assert s21.Peek(6) == 0x1c1;
      assert s21.Peek(10) == 0xb6;
      var s22 := Push2(s21, 0x03dd);
      var s23 := Swap2(s22);
      var s24 := Push1(s23, 0x04);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0814);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s27, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 136
    * Starting at 0x814
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x814 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x3dd

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x1c1

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3dd;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x1c1;
      assert s1.Peek(11) == 0xb6;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x3dd;
      assert s11.Peek(9) == 0x182;
      assert s11.Peek(11) == 0x1c1;
      assert s11.Peek(15) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0833);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0781);
      assert s21.Peek(0) == 0x781;
      assert s21.Peek(4) == 0x833;
      assert s21.Peek(9) == 0x3dd;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x1c1;
      assert s21.Peek(18) == 0xb6;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s22, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 129
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x833

    requires s0.stack[8] == 0x3dd

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x1c1

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x833;
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x1c1;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s146(s2, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 130
    * Starting at 0x784
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x833

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x833;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s7, gas - 1)
      else
        ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 131
    * Starting at 0x78d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x833

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x833;
      assert s1.Peek(10) == 0x3dd;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x1c1;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0784);
      assert s11.Peek(0) == 0x784;
      assert s11.Peek(5) == 0x833;
      assert s11.Peek(10) == 0x3dd;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x1c1;
      assert s11.Peek(19) == 0xb6;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s12, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 132
    * Starting at 0x79c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x833

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x1c1

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x833;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x1c1;
      assert s1.Peek(18) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s8, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 137
    * Starting at 0x833
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x833 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x3dd

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0x1c1

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0x1c1;
      assert s1.Peek(13) == 0xb6;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x3dd;
      assert s11.Peek(7) == 0x182;
      assert s11.Peek(9) == 0x1c1;
      assert s11.Peek(13) == 0xb6;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s17, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 73
    * Starting at 0x3dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x1c1

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(9) == 0xb6;
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

  /** Node 151
    * Segment Id for this node is: 74
    * Starting at 0x3e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x1c1

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x182;
      assert s1.Peek(4) == 0x1c1;
      assert s1.Peek(8) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s4, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 39
    * Starting at 0x182
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x1c1

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1c1;
      assert s1.Peek(5) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s3, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 46
    * Starting at 0x1c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x0174);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x02f9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s6, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 63
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x174

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x174;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push2(s1, 0x031a);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0305);
      var s5 := Push2(s4, 0x0357);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s6, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x305

    requires s0.stack[2] == 0x31a

    requires s0.stack[5] == 0x174

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x305;
      assert s1.Peek(2) == 0x31a;
      assert s1.Peek(5) == 0x174;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s4, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 64
    * Starting at 0x305
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x305 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31a

    requires s0.stack[5] == 0x174

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31a;
      assert s1.Peek(5) == 0x174;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x31a;
      assert s11.Peek(6) == 0x174;
      assert s11.Peek(10) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x042a);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s16, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 79
    * Starting at 0x42a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31a

    requires s0.stack[5] == 0x174

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31a;
      assert s1.Peek(5) == 0x174;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x31a;
      assert s11.Peek(9) == 0x174;
      assert s11.Peek(13) == 0xb6;
      var s12 := Push2(s11, 0x0645);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s13, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 109
    * Starting at 0x645
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x645 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x31a

    requires s0.stack[9] == 0x174

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x31a;
      assert s1.Peek(9) == 0x174;
      assert s1.Peek(13) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x191;
      assert s11.Peek(8) == 0x31a;
      assert s11.Peek(11) == 0x174;
      assert s11.Peek(15) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0703);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s18, gas - 1)
      else
        ExecuteFromCFGNode_s159(s18, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 110
    * Starting at 0x65d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x31a

    requires s0.stack[11] == 0x174

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x191;
      assert s1.Peek(9) == 0x31a;
      assert s1.Peek(12) == 0x174;
      assert s1.Peek(16) == 0xb6;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup6(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x00);
      var s8 := Not(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x191;
      assert s11.Peek(12) == 0x31a;
      assert s11.Peek(15) == 0x174;
      assert s11.Peek(19) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x0677);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s15, gas - 1)
      else
        ExecuteFromCFGNode_s160(s15, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 111
    * Starting at 0x670
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x670 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x31a

    requires s0.stack[14] == 0x174

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0677);
      assert s1.Peek(0) == 0x677;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x31a;
      assert s1.Peek(15) == 0x174;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s161(s3, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x677

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x31a

    requires s0.stack[15] == 0x174

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x677;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x31a;
      assert s1.Peek(15) == 0x174;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x677;
      assert s11.Peek(10) == 0x191;
      assert s11.Peek(14) == 0x31a;
      assert s11.Peek(17) == 0x174;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 162
    * Segment Id for this node is: 112
    * Starting at 0x677
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x677 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x31a

    requires s0.stack[14] == 0x174

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x31a;
      assert s1.Peek(14) == 0x174;
      assert s1.Peek(18) == 0xb6;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push1(s5, 0x00);
      var s7 := Keccak256(s6);
      var s8 := Add(s7);
      var s9 := SLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x191;
      assert s11.Peek(9) == 0x31a;
      assert s11.Peek(12) == 0x174;
      assert s11.Peek(16) == 0xb6;
      var s12 := Dup1(s11);
      var s13 := Dup6(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Dup5(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(10) == 0x191;
      assert s21.Peek(14) == 0x31a;
      assert s21.Peek(17) == 0x174;
      assert s21.Peek(21) == 0xb6;
      var s22 := Lt(s21);
      var s23 := Push2(s22, 0x069d);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s24, gas - 1)
      else
        ExecuteFromCFGNode_s163(s24, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 113
    * Starting at 0x696
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x696 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x31a

    requires s0.stack[15] == 0x174

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x069d);
      assert s1.Peek(0) == 0x69d;
      assert s1.Peek(9) == 0x191;
      assert s1.Peek(13) == 0x31a;
      assert s1.Peek(16) == 0x174;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s3, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x69d

    requires s0.stack[9] == 0x191

    requires s0.stack[13] == 0x31a

    requires s0.stack[16] == 0x174

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69d;
      assert s1.Peek(9) == 0x191;
      assert s1.Peek(13) == 0x31a;
      assert s1.Peek(16) == 0x174;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x69d;
      assert s11.Peek(11) == 0x191;
      assert s11.Peek(15) == 0x31a;
      assert s11.Peek(18) == 0x174;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 165
    * Segment Id for this node is: 114
    * Starting at 0x69d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x31a

    requires s0.stack[15] == 0x174

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x31a;
      assert s1.Peek(15) == 0x174;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := Keccak256(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x191;
      assert s11.Peek(14) == 0x31a;
      assert s11.Peek(17) == 0x174;
      assert s11.Peek(21) == 0xb6;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap1(s13);
      var s15 := Swap3(s14);
      var s16 := SStore(s15);
      var s17 := Swap2(s16);
      var s18 := Dup3(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Dup7(s20);
      assert s21.Peek(8) == 0x191;
      assert s21.Peek(12) == 0x31a;
      assert s21.Peek(15) == 0x174;
      assert s21.Peek(19) == 0xb6;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := Swap1(s25);
      var s27 := Keccak256(s26);
      var s28 := Dup2(s27);
      var s29 := Swap1(s28);
      var s30 := SStore(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(5) == 0x191;
      assert s31.Peek(9) == 0x31a;
      assert s31.Peek(12) == 0x174;
      assert s31.Peek(16) == 0xb6;
      var s32 := SLoad(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Dup1(s34);
      var s36 := Push2(s35, 0x06cf);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s37, gas - 1)
      else
        ExecuteFromCFGNode_s166(s37, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 115
    * Starting at 0x6c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x31a

    requires s0.stack[13] == 0x174

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06cf);
      assert s1.Peek(0) == 0x6cf;
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x31a;
      assert s1.Peek(14) == 0x174;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x08b3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s3, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 145
    * Starting at 0x8b3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x6cf

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x31a

    requires s0.stack[14] == 0x174

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6cf;
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x31a;
      assert s1.Peek(14) == 0x174;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x31);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x6cf;
      assert s11.Peek(9) == 0x191;
      assert s11.Peek(13) == 0x31a;
      assert s11.Peek(16) == 0x174;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 168
    * Segment Id for this node is: 116
    * Starting at 0x6cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x31a

    requires s0.stack[13] == 0x174

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x31a;
      assert s1.Peek(13) == 0x174;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(9) == 0x191;
      assert s11.Peek(13) == 0x31a;
      assert s11.Peek(16) == 0x174;
      assert s11.Peek(20) == 0xb6;
      var s12 := Keccak256(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := Swap1(s16);
      var s18 := SStore(s17);
      var s19 := Dup4(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x191;
      assert s21.Peek(9) == 0x31a;
      assert s21.Peek(12) == 0x174;
      assert s21.Peek(16) == 0xb6;
      var s22 := Push1(s21, 0x00);
      var s23 := Dup5(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(6) == 0x191;
      assert s31.Peek(10) == 0x31a;
      assert s31.Peek(13) == 0x174;
      assert s31.Peek(17) == 0xb6;
      var s32 := Add(s31);
      var s33 := Push1(s32, 0x00);
      var s34 := Keccak256(s33);
      var s35 := Push1(s34, 0x00);
      var s36 := Swap1(s35);
      var s37 := SStore(s36);
      var s38 := Push1(s37, 0x01);
      var s39 := Swap2(s38);
      var s40 := Pop(s39);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s169(s40, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 117
    * Starting at 0x703
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x31a

    requires s0.stack[11] == 0x174

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x31a;
      assert s1.Peek(11) == 0x174;
      assert s1.Peek(15) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s7, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x31a

    requires s0.stack[7] == 0x174

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x31a;
      assert s1.Peek(7) == 0x174;
      assert s1.Peek(11) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s7, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 65
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x174

    requires s0.stack[7] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x174;
      assert s1.Peek(7) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x174;
      assert s11.Peek(9) == 0xb6;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Dup5(s14);
      var s16 := Swap1(s15);
      var s17 := Push32(s16, 0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Swap1(s19);
      var s21 := Log4(s20);
      assert s21.Peek(2) == 0x174;
      assert s21.Peek(6) == 0xb6;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s24, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 37
    * Starting at 0x174
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x174 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s5, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 27
    * Starting at 0x119
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x119 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0090);
      var s3 := Push2(s2, 0x0127);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x070a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s7, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 118
    * Starting at 0x70a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x127

    requires s0.stack[3] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x127;
      assert s1.Peek(3) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x071c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s10, gas - 1)
      else
        ExecuteFromCFGNode_s175(s10, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 119
    * Starting at 0x718
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x718 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x127

    requires s0.stack[4] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x127;
      assert s1.Peek(5) == 0x90;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 176
    * Segment Id for this node is: 120
    * Starting at 0x71c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x127

    requires s0.stack[4] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x127;
      assert s1.Peek(4) == 0x90;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s7, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 28
    * Starting at 0x127
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x127 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x90;
      var s2 := Push2(s1, 0x01a4);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s3, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 43
    * Starting at 0x1a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0152);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02d8);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s6, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 61
    * Starting at 0x2d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x152

    requires s0.stack[4] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x152;
      assert s1.Peek(4) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0152);
      var s4 := Push2(s3, 0x02e5);
      var s5 := Push2(s4, 0x0357);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s6, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x2e5

    requires s0.stack[1] == 0x152

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2e5;
      assert s1.Peek(1) == 0x152;
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(7) == 0x90;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s4, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 62
    * Starting at 0x2e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x152

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x152;
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(7) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup5(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(5) == 0x152;
      assert s11.Peek(8) == 0x90;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Push2(s13, 0x0420);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s15, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 78
    * Starting at 0x420
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x152

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x152;
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(7) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0152);
      var s4 := Dup3(s3);
      var s5 := SLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s7, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x152

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x152;
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x90;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s6, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x152

    requires s0.stack[6] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x152;
      assert s1.Peek(6) == 0x90;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x90;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s6, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 14
    * Starting at 0x90
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90 as nat
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
      ExecuteFromCFGNode_s187(s8, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 15
    * Starting at 0x9a
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a as nat
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

  /** Node 188
    * Segment Id for this node is: 24
    * Starting at 0xf6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0109);
      var s3 := Push2(s2, 0x0104);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0723);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s7, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 121
    * Starting at 0x723
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x104

    requires s0.stack[3] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x104;
      assert s1.Peek(3) == 0x109;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0736);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s11, gas - 1)
      else
        ExecuteFromCFGNode_s190(s11, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 122
    * Starting at 0x732
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x732 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x104

    requires s0.stack[5] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x104;
      assert s1.Peek(6) == 0x109;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 191
    * Segment Id for this node is: 123
    * Starting at 0x736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x104

    requires s0.stack[5] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x104;
      assert s1.Peek(5) == 0x109;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0x104;
      assert s11.Peek(8) == 0x109;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := Dup2(s14);
      var s16 := And(s15);
      var s17 := Dup2(s16);
      var s18 := Eq(s17);
      var s19 := Push2(s18, 0x0754);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s20, gas - 1)
      else
        ExecuteFromCFGNode_s192(s20, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 124
    * Starting at 0x750
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x750 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x104

    requires s0.stack[6] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x104;
      assert s1.Peek(7) == 0x109;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 193
    * Segment Id for this node is: 125
    * Starting at 0x754
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x754 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x104

    requires s0.stack[6] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x104;
      assert s1.Peek(6) == 0x109;
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
      ExecuteFromCFGNode_s194(s11, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 25
    * Starting at 0x104
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x104 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109;
      var s2 := Push2(s1, 0x0198);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s3, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 42
    * Starting at 0x198
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x198 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x109;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x02b5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s7, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 59
    * Starting at 0x2b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x109;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c3);
      var s6 := Push2(s5, 0x0357);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s7, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x2c3

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2c3;
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x109;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s4, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 60
    * Starting at 0x2c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x109;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup7(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x109;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x040b);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s16, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 77
    * Starting at 0x40b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x109;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x191;
      assert s11.Peek(10) == 0x191;
      assert s11.Peek(14) == 0x109;
      var s12 := Push2(s11, 0x062d);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s13, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 108
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x191

    requires s0.stack[14] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x191;
      assert s1.Peek(14) == 0x109;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x191;
      assert s11.Peek(15) == 0x109;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s20, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x109;
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
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x109;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s7, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x109

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x109;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s7, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 26
    * Starting at 0x109
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x109 as nat
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
      var s11 := Push2(s10, 0x009a);
      assert s11.Peek(0) == 0x9a;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s12, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 21
    * Starting at 0xcb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00de);
      var s3 := Push2(s2, 0x00d9);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x075f);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s7, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 126
    * Starting at 0x75f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x75f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xd9

    requires s0.stack[3] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xd9;
      assert s1.Peek(3) == 0xde;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0772);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s208(s11, gas - 1)
      else
        ExecuteFromCFGNode_s207(s11, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 127
    * Starting at 0x76e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x76e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xd9

    requires s0.stack[5] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xd9;
      assert s1.Peek(6) == 0xde;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 208
    * Segment Id for this node is: 128
    * Starting at 0x772
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x772 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xd9

    requires s0.stack[5] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd9;
      assert s1.Peek(5) == 0xde;
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
      assert s11.Peek(1) == 0xd9;
      assert s11.Peek(4) == 0xde;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s14, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 22
    * Starting at 0xd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde;
      var s2 := Push2(s1, 0x0185);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s3, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 40
    * Starting at 0x185
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x185 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xde;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x0292);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s7, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 57
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0xde;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02a0);
      var s6 := Push2(s5, 0x0357);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s7, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[0] == 0x2a0

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a0;
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0xde;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s4, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 58
    * Starting at 0x2a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0xde;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup7(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0xde;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x03ff);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s16, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 76
    * Starting at 0x3ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0xde;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x05e1);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s7, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 103
    * Starting at 0x5e1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x191

    requires s0.stack[14] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x191;
      assert s1.Peek(14) == 0xde;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap1(s4);
      var s6 := Dup3(s5);
      var s7 := Lt(s6);
      var s8 := Push2(s7, 0x0605);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s217(s9, gas - 1)
      else
        ExecuteFromCFGNode_s216(s9, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 104
    * Starting at 0x5ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x191

    requires s0.stack[15] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x191;
      assert s1.Peek(16) == 0xde;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xe637bf3b);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(5) == 0x191;
      assert s11.Peek(9) == 0x191;
      assert s11.Peek(13) == 0x191;
      assert s11.Peek(17) == 0xde;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 217
    * Segment Id for this node is: 105
    * Starting at 0x605
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x605 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x191

    requires s0.stack[15] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x191;
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x191;
      assert s1.Peek(15) == 0xde;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Add(s3);
      var s5 := Dup3(s4);
      var s6 := Dup2(s5);
      var s7 := SLoad(s6);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x061a);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s11, gas - 1)
      else
        ExecuteFromCFGNode_s218(s11, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 106
    * Starting at 0x613
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x613 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x191

    requires s0.stack[9] == 0x191

    requires s0.stack[13] == 0x191

    requires s0.stack[17] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x061a);
      assert s1.Peek(0) == 0x61a;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x191;
      assert s1.Peek(14) == 0x191;
      assert s1.Peek(18) == 0xde;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s3, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x61a

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x191

    requires s0.stack[14] == 0x191

    requires s0.stack[18] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x61a;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x191;
      assert s1.Peek(14) == 0x191;
      assert s1.Peek(18) == 0xde;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x61a;
      assert s11.Peek(8) == 0x191;
      assert s11.Peek(12) == 0x191;
      assert s11.Peek(16) == 0x191;
      assert s11.Peek(20) == 0xde;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 220
    * Segment Id for this node is: 107
    * Starting at 0x61a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x191

    requires s0.stack[9] == 0x191

    requires s0.stack[13] == 0x191

    requires s0.stack[17] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x191;
      assert s1.Peek(9) == 0x191;
      assert s1.Peek(13) == 0x191;
      assert s1.Peek(17) == 0xde;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push1(s5, 0x00);
      var s7 := Keccak256(s6);
      var s8 := Add(s7);
      var s9 := SLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x191;
      assert s11.Peek(15) == 0xde;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s16, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0xde;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s7, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0xde;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s7, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xde

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xde;
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
    * Segment Id for this node is: 23
    * Starting at 0xde
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xde as nat
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
      var s16 := Push2(s15, 0x009a);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s17, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 19
    * Starting at 0xb8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b6);
      var s3 := Push2(s2, 0x00c6);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x070a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s7, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 118
    * Starting at 0x70a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xc6

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc6;
      assert s1.Peek(3) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x071c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s228(s10, gas - 1)
      else
        ExecuteFromCFGNode_s227(s10, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 119
    * Starting at 0x718
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x718 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xc6

    requires s0.stack[4] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xc6;
      assert s1.Peek(5) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 228
    * Segment Id for this node is: 120
    * Starting at 0x71c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xc6

    requires s0.stack[4] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xc6;
      assert s1.Peek(4) == 0xb6;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s7, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 20
    * Starting at 0xc6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb6;
      var s2 := Push2(s1, 0x0179);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s230(s3, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 38
    * Starting at 0x179
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb6;
      var s2 := Push2(s1, 0x0182);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0288);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s5, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 56
    * Starting at 0x288
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x288 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x182

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x182;
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x0182);
      var s3 := Dup2(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x02f9);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s6, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 63
    * Starting at 0x2f9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x182

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x182;
      assert s1.Peek(4) == 0x182;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push2(s1, 0x031a);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0305);
      var s5 := Push2(s4, 0x0357);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s6, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x305

    requires s0.stack[2] == 0x31a

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x305;
      assert s1.Peek(2) == 0x31a;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s4, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 64
    * Starting at 0x305
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x305 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31a

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31a;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x31a;
      assert s11.Peek(6) == 0x182;
      assert s11.Peek(8) == 0x182;
      assert s11.Peek(10) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x042a);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s16, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 79
    * Starting at 0x42a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x31a

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x31a;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x31a;
      assert s11.Peek(9) == 0x182;
      assert s11.Peek(11) == 0x182;
      assert s11.Peek(13) == 0xb6;
      var s12 := Push2(s11, 0x0645);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s13, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 109
    * Starting at 0x645
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x645 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x31a

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x31a;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x191;
      assert s11.Peek(8) == 0x31a;
      assert s11.Peek(11) == 0x182;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Dup1(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0703);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s247(s18, gas - 1)
      else
        ExecuteFromCFGNode_s237(s18, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 110
    * Starting at 0x65d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x31a

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(5) == 0x191;
      assert s1.Peek(9) == 0x31a;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0xb6;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap1(s3);
      var s5 := Dup6(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x00);
      var s8 := Not(s7);
      var s9 := Dup2(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(8) == 0x191;
      assert s11.Peek(12) == 0x31a;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x0677);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s240(s15, gas - 1)
      else
        ExecuteFromCFGNode_s238(s15, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 111
    * Starting at 0x670
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x670 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x31a

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x182

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0677);
      assert s1.Peek(0) == 0x677;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x31a;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x182;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s3, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x677

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x31a

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x182

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x677;
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x31a;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x182;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x677;
      assert s11.Peek(10) == 0x191;
      assert s11.Peek(14) == 0x31a;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x182;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 240
    * Segment Id for this node is: 112
    * Starting at 0x677
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x677 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x31a

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x182

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x31a;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x182;
      assert s1.Peek(18) == 0xb6;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push1(s5, 0x00);
      var s7 := Keccak256(s6);
      var s8 := Add(s7);
      var s9 := SLoad(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x191;
      assert s11.Peek(9) == 0x31a;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0xb6;
      var s12 := Dup1(s11);
      var s13 := Dup6(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Dup5(s16);
      var s18 := Sub(s17);
      var s19 := Dup2(s18);
      var s20 := SLoad(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(10) == 0x191;
      assert s21.Peek(14) == 0x31a;
      assert s21.Peek(17) == 0x182;
      assert s21.Peek(19) == 0x182;
      assert s21.Peek(21) == 0xb6;
      var s22 := Lt(s21);
      var s23 := Push2(s22, 0x069d);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s24, gas - 1)
      else
        ExecuteFromCFGNode_s241(s24, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 113
    * Starting at 0x696
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x696 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x31a

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x182

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x069d);
      assert s1.Peek(0) == 0x69d;
      assert s1.Peek(9) == 0x191;
      assert s1.Peek(13) == 0x31a;
      assert s1.Peek(16) == 0x182;
      assert s1.Peek(18) == 0x182;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s242(s3, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x69d

    requires s0.stack[9] == 0x191

    requires s0.stack[13] == 0x31a

    requires s0.stack[16] == 0x182

    requires s0.stack[18] == 0x182

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x69d;
      assert s1.Peek(9) == 0x191;
      assert s1.Peek(13) == 0x31a;
      assert s1.Peek(16) == 0x182;
      assert s1.Peek(18) == 0x182;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x69d;
      assert s11.Peek(11) == 0x191;
      assert s11.Peek(15) == 0x31a;
      assert s11.Peek(18) == 0x182;
      assert s11.Peek(20) == 0x182;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 243
    * Segment Id for this node is: 114
    * Starting at 0x69d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[8] == 0x191

    requires s0.stack[12] == 0x31a

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x182

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x191;
      assert s1.Peek(12) == 0x31a;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x182;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup1(s6);
      var s8 := Dup4(s7);
      var s9 := Keccak256(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x191;
      assert s11.Peek(14) == 0x31a;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x182;
      assert s11.Peek(21) == 0xb6;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap1(s13);
      var s15 := Swap3(s14);
      var s16 := SStore(s15);
      var s17 := Swap2(s16);
      var s18 := Dup3(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Dup7(s20);
      assert s21.Peek(8) == 0x191;
      assert s21.Peek(12) == 0x31a;
      assert s21.Peek(15) == 0x182;
      assert s21.Peek(17) == 0x182;
      assert s21.Peek(19) == 0xb6;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := Swap1(s25);
      var s27 := Keccak256(s26);
      var s28 := Dup2(s27);
      var s29 := Swap1(s28);
      var s30 := SStore(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(5) == 0x191;
      assert s31.Peek(9) == 0x31a;
      assert s31.Peek(12) == 0x182;
      assert s31.Peek(14) == 0x182;
      assert s31.Peek(16) == 0xb6;
      var s32 := SLoad(s31);
      var s33 := Dup5(s32);
      var s34 := Swap1(s33);
      var s35 := Dup1(s34);
      var s36 := Push2(s35, 0x06cf);
      var s37 := JumpI(s36);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s36.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s37, gas - 1)
      else
        ExecuteFromCFGNode_s244(s37, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 115
    * Starting at 0x6c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x31a

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x06cf);
      assert s1.Peek(0) == 0x6cf;
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x31a;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x182;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x08b3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s3, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 145
    * Starting at 0x8b3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x6cf

    requires s0.stack[7] == 0x191

    requires s0.stack[11] == 0x31a

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x182

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x6cf;
      assert s1.Peek(7) == 0x191;
      assert s1.Peek(11) == 0x31a;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x182;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x31);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x6cf;
      assert s11.Peek(9) == 0x191;
      assert s11.Peek(13) == 0x31a;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x182;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 246
    * Segment Id for this node is: 116
    * Starting at 0x6cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x31a

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x31a;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Swap1(s2);
      var s4 := Sub(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(9) == 0x191;
      assert s11.Peek(13) == 0x31a;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x182;
      assert s11.Peek(20) == 0xb6;
      var s12 := Keccak256(s11);
      var s13 := Add(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := Swap1(s16);
      var s18 := SStore(s17);
      var s19 := Dup4(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x191;
      assert s21.Peek(9) == 0x31a;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x182;
      assert s21.Peek(16) == 0xb6;
      var s22 := Push1(s21, 0x00);
      var s23 := Dup5(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Swap1(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(6) == 0x191;
      assert s31.Peek(10) == 0x31a;
      assert s31.Peek(13) == 0x182;
      assert s31.Peek(15) == 0x182;
      assert s31.Peek(17) == 0xb6;
      var s32 := Add(s31);
      var s33 := Push1(s32, 0x00);
      var s34 := Keccak256(s33);
      var s35 := Push1(s34, 0x00);
      var s36 := Swap1(s35);
      var s37 := SStore(s36);
      var s38 := Push1(s37, 0x01);
      var s39 := Swap2(s38);
      var s40 := Pop(s39);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s247(s40, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 117
    * Starting at 0x703
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x703 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x31a

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x31a;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s248(s7, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x31a

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x31a;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s7, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 65
    * Starting at 0x31a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x182;
      assert s11.Peek(7) == 0x182;
      assert s11.Peek(9) == 0xb6;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Dup5(s14);
      var s16 := Swap1(s15);
      var s17 := Push32(s16, 0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Swap1(s19);
      var s21 := Log4(s20);
      assert s21.Peek(2) == 0x182;
      assert s21.Peek(4) == 0x182;
      assert s21.Peek(6) == 0xb6;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s250(s24, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 39
    * Starting at 0x182
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x182

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x182;
      assert s1.Peek(3) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s3, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 39
    * Starting at 0x182
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00b6);
      var s3 := Push2(s2, 0x00b1);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0723);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s253(s7, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 121
    * Starting at 0x723
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x723 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xb1

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb1;
      assert s1.Peek(3) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0736);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s11, gas - 1)
      else
        ExecuteFromCFGNode_s254(s11, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 122
    * Starting at 0x732
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x732 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xb1

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xb1;
      assert s1.Peek(6) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 255
    * Segment Id for this node is: 123
    * Starting at 0x736
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x736 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xb1

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb1;
      assert s1.Peek(5) == 0xb6;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(7) == 0xb1;
      assert s11.Peek(8) == 0xb6;
      var s12 := Push1(s11, 0xa0);
      var s13 := Shl(s12);
      var s14 := Sub(s13);
      var s15 := Dup2(s14);
      var s16 := And(s15);
      var s17 := Dup2(s16);
      var s18 := Eq(s17);
      var s19 := Push2(s18, 0x0754);
      var s20 := JumpI(s19);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s19.stack[1] > 0 then
        ExecuteFromCFGNode_s257(s20, gas - 1)
      else
        ExecuteFromCFGNode_s256(s20, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 124
    * Starting at 0x750
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x750 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xb1

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0xb1;
      assert s1.Peek(7) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 257
    * Segment Id for this node is: 125
    * Starting at 0x754
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x754 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0xb1

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xb1;
      assert s1.Peek(6) == 0xb6;
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
      ExecuteFromCFGNode_s258(s11, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 17
    * Starting at 0xb1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb6;
      var s2 := Push2(s1, 0x0158);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s3, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 34
    * Starting at 0x158
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x158 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xb6;
      var s2 := Push2(s1, 0x0161);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0202);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s5, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 50
    * Starting at 0x202
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x161

    requires s0.stack[4] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x161;
      assert s1.Peek(4) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x020c);
      var s4 := Push2(s3, 0x0357);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s5, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x20c

    requires s0.stack[3] == 0x161

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x20c;
      assert s1.Peek(3) == 0x161;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s262(s4, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 51
    * Starting at 0x20c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x161

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x161;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap3(s2);
      var s4 := Dup4(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x161;
      assert s11.Peek(4) == 0xb6;
      var s12 := Push1(s11, 0x02);
      var s13 := Add(s12);
      var s14 := SLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s263(s16, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 35
    * Starting at 0x161
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x161 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x016a);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0220);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s5, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 52
    * Starting at 0x220
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x220 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x16a

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x16a;
      assert s1.Peek(5) == 0xb6;
      var s2 := Push2(s1, 0x0182);
      var s3 := Dup2(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x037b);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s6, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 67
    * Starting at 0x37b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x16a

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x182;
      assert s1.Peek(4) == 0x16a;
      assert s1.Peek(8) == 0xb6;
      var s2 := Push2(s1, 0x0385);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02b5);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s6, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 59
    * Starting at 0x2b5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x385

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x16a

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x385;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x16a;
      assert s1.Peek(11) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02c3);
      var s6 := Push2(s5, 0x0357);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s7, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x2c3

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x385

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2c3;
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x385;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s4, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 60
    * Starting at 0x2c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x385

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x385;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup7(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x385;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x16a;
      assert s11.Peek(16) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x040b);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s16, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 77
    * Starting at 0x40b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x385

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x385;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x191;
      assert s11.Peek(10) == 0x385;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x16a;
      assert s11.Peek(19) == 0xb6;
      var s12 := Push2(s11, 0x062d);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s13, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 108
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x385

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x385;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x191;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x385;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s20, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x385

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x385;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s272(s7, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x385

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0x16a

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x385;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0x16a;
      assert s1.Peek(13) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s7, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 68
    * Starting at 0x385
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x385 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x16a

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x16a;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push2(s1, 0x03e6);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s3, gas - 1)
      else
        ExecuteFromCFGNode_s274(s3, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 69
    * Starting at 0x38a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x16a

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x039b);
      assert s1.Peek(0) == 0x39b;
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x16a;
      assert s1.Peek(9) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x043f);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s10, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 80
    * Starting at 0x43f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x39b

    requires s0.stack[4] == 0x182

    requires s0.stack[6] == 0x16a

    requires s0.stack[10] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x39b;
      assert s1.Peek(4) == 0x182;
      assert s1.Peek(6) == 0x16a;
      assert s1.Peek(10) == 0xb6;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0152);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup4(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x14);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s276(s11, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 81
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x152

    requires s0.stack[5] == 0x39b

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x16a

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x152;
      assert s1.Peek(5) == 0x39b;
      assert s1.Peek(8) == 0x182;
      assert s1.Peek(10) == 0x16a;
      assert s1.Peek(14) == 0xb6;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0460);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push2(s6, 0x085d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s8, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 139
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x460

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x460;
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
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
      assert s11.Peek(5) == 0x460;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x16a;
      assert s11.Peek(22) == 0xb6;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0152);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s280(s14, gas - 1)
      else
        ExecuteFromCFGNode_s278(s14, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 140
    * Starting at 0x86d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s3, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x460

    requires s0.stack[9] == 0x152

    requires s0.stack[12] == 0x39b

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x16a

    requires s0.stack[21] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x460;
      assert s11.Peek(11) == 0x152;
      assert s11.Peek(14) == 0x39b;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x16a;
      assert s11.Peek(23) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 280
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x460;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s6, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 82
    * Starting at 0x460
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push2(s1, 0x046b);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Push2(s4, 0x0874);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s6, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 141
    * Starting at 0x874
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x874 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[2] == 0x46b

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x46b;
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0152);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s285(s10, gas - 1)
      else
        ExecuteFromCFGNode_s283(s10, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 142
    * Starting at 0x880
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x880 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s3, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x46b

    requires s0.stack[9] == 0x152

    requires s0.stack[12] == 0x39b

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x16a

    requires s0.stack[21] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x46b;
      assert s11.Peek(11) == 0x152;
      assert s11.Peek(14) == 0x39b;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x16a;
      assert s11.Peek(23) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 285
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x46b;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 83
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x40);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0482);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s289(s11, gas - 1)
      else
        ExecuteFromCFGNode_s287(s11, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 84
    * Starting at 0x47b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0482);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x0887);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s288(s3, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 143
    * Starting at 0x887
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x887 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x482

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x39b

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x482;
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 289
    * Segment Id for this node is: 85
    * Starting at 0x482
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x152;
      assert s21.Peek(10) == 0x39b;
      assert s21.Peek(13) == 0x182;
      assert s21.Peek(15) == 0x16a;
      assert s21.Peek(19) == 0xb6;
      var s22 := Push2(s21, 0x04ac);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s23, gas - 1)
      else
        ExecuteFromCFGNode_s290(s23, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 86
    * Starting at 0x4a0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x39b

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Dup4(s6);
      var s8 := CallDataCopy(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s291(s11, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 87
    * Starting at 0x4ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x152

    requires s0.stack[9] == 0x39b

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push1(s5, 0xfc);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x04c7);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s15, gas - 1)
      else
        ExecuteFromCFGNode_s292(s15, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 88
    * Starting at 0x4c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04c7);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s3, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4c7

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4c7;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x16a;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 294
    * Segment Id for this node is: 89
    * Starting at 0x4c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
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
      assert s11.Peek(7) == 0x152;
      assert s11.Peek(10) == 0x39b;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x16a;
      assert s11.Peek(19) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x0f);
      var s21 := Push1(s20, 0xfb);
      assert s21.Peek(6) == 0x152;
      assert s21.Peek(9) == 0x39b;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x16a;
      assert s21.Peek(18) == 0xb6;
      var s22 := Shl(s21);
      var s23 := Dup2(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Dup2(s24);
      var s26 := MLoad(s25);
      var s27 := Dup2(s26);
      var s28 := Lt(s27);
      var s29 := Push2(s28, 0x04f6);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s297(s30, gas - 1)
      else
        ExecuteFromCFGNode_s295(s30, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 90
    * Starting at 0x4ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f6);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s296(s3, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x4f6

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f6;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x16a;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 297
    * Segment Id for this node is: 91
    * Starting at 0x4f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
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
      assert s11.Peek(7) == 0x152;
      assert s11.Peek(10) == 0x39b;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x16a;
      assert s11.Peek(19) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(6) == 0x152;
      assert s21.Peek(9) == 0x39b;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x16a;
      assert s21.Peek(18) == 0xb6;
      var s22 := Dup5(s21);
      var s23 := Mul(s22);
      var s24 := Add(s23);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s298(s24, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 92
    * Starting at 0x515
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x515 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0583);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s306(s7, gas - 1)
      else
        ExecuteFromCFGNode_s299(s7, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 93
    * Starting at 0x51f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 16, 0x181899199a1a9b1b9c1cb0b131b232b3);
      assert s1.Peek(6) == 0x152;
      assert s1.Peek(9) == 0x39b;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push1(s1, 0x81);
      var s3 := Shl(s2);
      var s4 := Dup6(s3);
      var s5 := Push1(s4, 0x0f);
      var s6 := And(s5);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x0546);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s302(s11, gas - 1)
      else
        ExecuteFromCFGNode_s300(s11, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 94
    * Starting at 0x53f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0546);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s301(s3, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x546

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x546;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x16a;
      assert s11.Peek(22) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 302
    * Segment Id for this node is: 95
    * Starting at 0x546
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x546 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x152

    requires s0.stack[10] == 0x39b

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x152;
      assert s1.Peek(10) == 0x39b;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Byte(s1);
      var s3 := Push1(s2, 0xf8);
      var s4 := Shl(s3);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Dup2(s6);
      var s8 := MLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Lt(s9);
      var s11 := Push2(s10, 0x055c);
      assert s11.Peek(0) == 0x55c;
      assert s11.Peek(10) == 0x152;
      assert s11.Peek(13) == 0x39b;
      assert s11.Peek(16) == 0x182;
      assert s11.Peek(18) == 0x16a;
      assert s11.Peek(22) == 0xb6;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s305(s12, gas - 1)
      else
        ExecuteFromCFGNode_s303(s12, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 96
    * Starting at 0x555
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x555 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x055c);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s304(s3, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x55c

    requires s0.stack[9] == 0x152

    requires s0.stack[12] == 0x39b

    requires s0.stack[15] == 0x182

    requires s0.stack[17] == 0x16a

    requires s0.stack[21] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x152;
      assert s1.Peek(12) == 0x39b;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x55c;
      assert s11.Peek(11) == 0x152;
      assert s11.Peek(14) == 0x39b;
      assert s11.Peek(17) == 0x182;
      assert s11.Peek(19) == 0x16a;
      assert s11.Peek(23) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 305
    * Segment Id for this node is: 97
    * Starting at 0x55c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x152

    requires s0.stack[11] == 0x39b

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x152;
      assert s1.Peek(11) == 0x39b;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
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
      assert s11.Peek(8) == 0x152;
      assert s11.Peek(11) == 0x39b;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x04);
      var s21 := Swap5(s20);
      assert s21.Peek(6) == 0x152;
      assert s21.Peek(9) == 0x39b;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x16a;
      assert s21.Peek(18) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := Swap5(s22);
      var s24 := Shr(s23);
      var s25 := Swap4(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Not(s26);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0515);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s298(s30, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 98
    * Starting at 0x583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x152

    requires s0.stack[8] == 0x39b

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0191);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s308(s6, gas - 1)
      else
        ExecuteFromCFGNode_s307(s6, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 99
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x39b

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x16a

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x152;
      assert s1.Peek(8) == 0x39b;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xc9134785);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(6) == 0x152;
      assert s11.Peek(9) == 0x39b;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x16a;
      assert s11.Peek(18) == 0xb6;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 308
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[4] == 0x152

    requires s0.stack[7] == 0x39b

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x16a

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x152;
      assert s1.Peek(7) == 0x39b;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x16a;
      assert s1.Peek(16) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s309(s7, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x39b

    requires s0.stack[6] == 0x182

    requires s0.stack[8] == 0x16a

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x39b;
      assert s1.Peek(6) == 0x182;
      assert s1.Peek(8) == 0x16a;
      assert s1.Peek(12) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s6, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 70
    * Starting at 0x39b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x16a

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x16a;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push2(s1, 0x03a6);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push2(s4, 0x0451);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s311(s6, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 81
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x3a6

    requires s0.stack[6] == 0x182

    requires s0.stack[8] == 0x16a

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3a6;
      assert s1.Peek(6) == 0x182;
      assert s1.Peek(8) == 0x16a;
      assert s1.Peek(12) == 0xb6;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x0460);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x02);
      var s7 := Push2(s6, 0x085d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s8, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 139
    * Starting at 0x85d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x460

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x460;
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
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
      assert s11.Peek(5) == 0x460;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Or(s11);
      var s13 := Push2(s12, 0x0152);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s315(s14, gas - 1)
      else
        ExecuteFromCFGNode_s313(s14, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 140
    * Starting at 0x86d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x86d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s314(s3, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x460

    requires s0.stack[9] == 0x3a6

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x460;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x460;
      assert s11.Peek(11) == 0x3a6;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x16a;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 315
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x460

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x460;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s316(s6, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 82
    * Starting at 0x460
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push2(s1, 0x046b);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Push2(s4, 0x0874);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s6, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 141
    * Starting at 0x874
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x874 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x46b

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x46b;
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Dup1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0152);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s320(s10, gas - 1)
      else
        ExecuteFromCFGNode_s318(s10, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 142
    * Starting at 0x880
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x880 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0152);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x0847);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s319(s3, gas - 1)
  }

  /** Node 319
    * Segment Id for this node is: 138
    * Starting at 0x847
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x847 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x152

    requires s0.stack[4] == 0x46b

    requires s0.stack[9] == 0x3a6

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x152;
      assert s1.Peek(4) == 0x46b;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x11);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x152;
      assert s11.Peek(6) == 0x46b;
      assert s11.Peek(11) == 0x3a6;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x16a;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 320
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x46b

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x46b;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s321(s6, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 83
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x40);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0482);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s324(s11, gas - 1)
      else
        ExecuteFromCFGNode_s322(s11, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 84
    * Starting at 0x47b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0482);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x16a;
      assert s1.Peek(16) == 0xb6;
      var s2 := Push2(s1, 0x0887);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s323(s3, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 143
    * Starting at 0x887
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x887 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x482

    requires s0.stack[6] == 0x3a6

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x16a

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x482;
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x16a;
      assert s1.Peek(16) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x482;
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x16a;
      assert s11.Peek(18) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 324
    * Segment Id for this node is: 85
    * Starting at 0x482
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x1f);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x1f);
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x16a;
      assert s11.Peek(18) == 0xb6;
      var s12 := Not(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x3a6;
      assert s21.Peek(11) == 0x182;
      assert s21.Peek(13) == 0x16a;
      assert s21.Peek(17) == 0xb6;
      var s22 := Push2(s21, 0x04ac);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s326(s23, gas - 1)
      else
        ExecuteFromCFGNode_s325(s23, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 86
    * Starting at 0x4a0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x3a6

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x16a

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup2(s3);
      var s5 := Dup1(s4);
      var s6 := CallDataSize(s5);
      var s7 := Dup4(s6);
      var s8 := CallDataCopy(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s326(s11, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 87
    * Starting at 0x4ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[6] == 0x3a6

    requires s0.stack[10] == 0x182

    requires s0.stack[12] == 0x16a

    requires s0.stack[16] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x16a;
      assert s1.Peek(16) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x03);
      var s6 := Push1(s5, 0xfc);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup2(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x16a;
      assert s11.Peek(18) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := Lt(s12);
      var s14 := Push2(s13, 0x04c7);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s15, gas - 1)
      else
        ExecuteFromCFGNode_s327(s15, gas - 1)
  }

  /** Node 327
    * Segment Id for this node is: 88
    * Starting at 0x4c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04c7);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s328(s3, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x4c7

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4c7;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4c7;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 329
    * Segment Id for this node is: 89
    * Starting at 0x4c7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
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
      assert s11.Peek(7) == 0x3a6;
      assert s11.Peek(11) == 0x182;
      assert s11.Peek(13) == 0x16a;
      assert s11.Peek(17) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x0f);
      var s21 := Push1(s20, 0xfb);
      assert s21.Peek(6) == 0x3a6;
      assert s21.Peek(10) == 0x182;
      assert s21.Peek(12) == 0x16a;
      assert s21.Peek(16) == 0xb6;
      var s22 := Shl(s21);
      var s23 := Dup2(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Dup2(s24);
      var s26 := MLoad(s25);
      var s27 := Dup2(s26);
      var s28 := Lt(s27);
      var s29 := Push2(s28, 0x04f6);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s30, gas - 1)
      else
        ExecuteFromCFGNode_s330(s30, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 90
    * Starting at 0x4ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04f6);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s331(s3, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x4f6

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x4f6;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 332
    * Segment Id for this node is: 91
    * Starting at 0x4f6
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
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
      assert s11.Peek(7) == 0x3a6;
      assert s11.Peek(11) == 0x182;
      assert s11.Peek(13) == 0x16a;
      assert s11.Peek(17) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x01);
      var s21 := Push1(s20, 0x02);
      assert s21.Peek(6) == 0x3a6;
      assert s21.Peek(10) == 0x182;
      assert s21.Peek(12) == 0x16a;
      assert s21.Peek(16) == 0xb6;
      var s22 := Dup5(s21);
      var s23 := Mul(s22);
      var s24 := Add(s23);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s333(s24, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 92
    * Starting at 0x515
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x515 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0583);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s341(s7, gas - 1)
      else
        ExecuteFromCFGNode_s334(s7, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 93
    * Starting at 0x51f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 16, 0x181899199a1a9b1b9c1cb0b131b232b3);
      assert s1.Peek(6) == 0x3a6;
      assert s1.Peek(10) == 0x182;
      assert s1.Peek(12) == 0x16a;
      assert s1.Peek(16) == 0xb6;
      var s2 := Push1(s1, 0x81);
      var s3 := Shl(s2);
      var s4 := Dup6(s3);
      var s5 := Push1(s4, 0x0f);
      var s6 := And(s5);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := Push2(s9, 0x0546);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s337(s11, gas - 1)
      else
        ExecuteFromCFGNode_s335(s11, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 94
    * Starting at 0x53f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0546);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s3, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x546

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x546;
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x546;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 337
    * Segment Id for this node is: 95
    * Starting at 0x546
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x546 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x3a6

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3a6;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Byte(s1);
      var s3 := Push1(s2, 0xf8);
      var s4 := Shl(s3);
      var s5 := Dup3(s4);
      var s6 := Dup3(s5);
      var s7 := Dup2(s6);
      var s8 := MLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Lt(s9);
      var s11 := Push2(s10, 0x055c);
      assert s11.Peek(0) == 0x55c;
      assert s11.Peek(10) == 0x3a6;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s340(s12, gas - 1)
      else
        ExecuteFromCFGNode_s338(s12, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 96
    * Starting at 0x555
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x555 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x055c);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push2(s1, 0x089d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s3, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 144
    * Starting at 0x89d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x55c

    requires s0.stack[9] == 0x3a6

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x55c;
      assert s1.Peek(9) == 0x3a6;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x32);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x55c;
      assert s11.Peek(11) == 0x3a6;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x16a;
      assert s11.Peek(21) == 0xb6;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 340
    * Segment Id for this node is: 97
    * Starting at 0x55c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x3a6

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x3a6;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
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
      assert s11.Peek(8) == 0x3a6;
      assert s11.Peek(12) == 0x182;
      assert s11.Peek(14) == 0x16a;
      assert s11.Peek(18) == 0xb6;
      var s12 := And(s11);
      var s13 := Swap1(s12);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Byte(s15);
      var s17 := Swap1(s16);
      var s18 := MStore8(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x04);
      var s21 := Swap5(s20);
      assert s21.Peek(6) == 0x3a6;
      assert s21.Peek(10) == 0x182;
      assert s21.Peek(12) == 0x16a;
      assert s21.Peek(16) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := Swap5(s22);
      var s24 := Shr(s23);
      var s25 := Swap4(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Not(s26);
      var s28 := Add(s27);
      var s29 := Push2(s28, 0x0515);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s30, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 98
    * Starting at 0x583
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x3a6

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0191);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s6, gas - 1)
      else
        ExecuteFromCFGNode_s342(s6, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 99
    * Starting at 0x58b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x3a6

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x16a

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(5) == 0x3a6;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0xc9134785);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(6) == 0x3a6;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x16a;
      assert s11.Peek(16) == 0xb6;
      var s12 := Dup1(s11);
      var s13 := Swap2(s12);
      var s14 := Sub(s13);
      var s15 := Swap1(s14);
      var s16 := Revert(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 343
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x3a6

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x16a

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3a6;
      assert s1.Peek(8) == 0x182;
      assert s1.Peek(10) == 0x16a;
      assert s1.Peek(14) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s7, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 71
    * Starting at 0x3a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x182

    requires s0.stack[6] == 0x16a

    requires s0.stack[10] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x182;
      assert s1.Peek(6) == 0x16a;
      assert s1.Peek(10) == 0xb6;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Push2(s5, 0x03b7);
      var s7 := Swap3(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x07a5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s11, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 133
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x3b7

    requires s0.stack[6] == 0x182

    requires s0.stack[8] == 0x16a

    requires s0.stack[12] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3b7;
      assert s1.Peek(6) == 0x182;
      assert s1.Peek(8) == 0x16a;
      assert s1.Peek(12) == 0xb6;
      var s2 := PushN(s1, 23, 0x020b1b1b2b9b9a1b7b73a3937b61d1030b1b1b7bab73a1);
      var s3 := Push1(s2, 0x4d);
      var s4 := Shl(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x00);
      var s8 := Dup4(s7);
      var s9 := MLoad(s8);
      var s10 := Push2(s9, 0x07d7);
      var s11 := Dup2(s10);
      assert s11.Peek(1) == 0x7d7;
      assert s11.Peek(7) == 0x3b7;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x16a;
      assert s11.Peek(16) == 0xb6;
      var s12 := Push1(s11, 0x17);
      var s13 := Dup6(s12);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup9(s15);
      var s17 := Add(s16);
      var s18 := Push2(s17, 0x0781);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s346(s19, gas - 1)
  }

  /** Node 346
    * Segment Id for this node is: 129
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x7d7

    requires s0.stack[9] == 0x3b7

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7d7;
      assert s1.Peek(9) == 0x3b7;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s347(s2, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 130
    * Starting at 0x784
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x7d7

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s7, gas - 1)
      else
        ExecuteFromCFGNode_s348(s7, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 131
    * Starting at 0x78d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x7d7

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x7d7;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0784);
      assert s11.Peek(0) == 0x784;
      assert s11.Peek(5) == 0x7d7;
      assert s11.Peek(11) == 0x3b7;
      assert s11.Peek(14) == 0x182;
      assert s11.Peek(16) == 0x16a;
      assert s11.Peek(20) == 0xb6;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s12, gas - 1)
  }

  /** Node 349
    * Segment Id for this node is: 132
    * Starting at 0x79c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[4] == 0x7d7

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s8, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 134
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x3b7

    requires s0.stack[8] == 0x182

    requires s0.stack[10] == 0x16a

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3b7;
      assert s1.Peek(8) == 0x182;
      assert s1.Peek(10) == 0x16a;
      assert s1.Peek(14) == 0xb6;
      var s2 := PushN(s1, 17, 0x01034b99036b4b9b9b4b733903937b6329);
      var s3 := Push1(s2, 0x7d);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x17);
      var s6 := Swap2(s5);
      var s7 := Dup5(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Dup3(s9);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x3b7;
      assert s11.Peek(10) == 0x182;
      assert s11.Peek(12) == 0x16a;
      assert s11.Peek(16) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Dup4(s12);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0808);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x28);
      var s18 := Dup5(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup9(s20);
      assert s21.Peek(4) == 0x808;
      assert s21.Peek(11) == 0x3b7;
      assert s21.Peek(14) == 0x182;
      assert s21.Peek(16) == 0x16a;
      assert s21.Peek(20) == 0xb6;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0781);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s24, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 129
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[3] == 0x808

    requires s0.stack[10] == 0x3b7

    requires s0.stack[13] == 0x182

    requires s0.stack[15] == 0x16a

    requires s0.stack[19] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x808;
      assert s1.Peek(10) == 0x3b7;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s352(s2, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 130
    * Starting at 0x784
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x808

    requires s0.stack[11] == 0x3b7

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x808;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s354(s7, gas - 1)
      else
        ExecuteFromCFGNode_s353(s7, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 131
    * Starting at 0x78d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x808

    requires s0.stack[11] == 0x3b7

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x808;
      assert s1.Peek(12) == 0x3b7;
      assert s1.Peek(15) == 0x182;
      assert s1.Peek(17) == 0x16a;
      assert s1.Peek(21) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0784);
      assert s11.Peek(0) == 0x784;
      assert s11.Peek(5) == 0x808;
      assert s11.Peek(12) == 0x3b7;
      assert s11.Peek(15) == 0x182;
      assert s11.Peek(17) == 0x16a;
      assert s11.Peek(21) == 0xb6;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s12, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 132
    * Starting at 0x79c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[4] == 0x808

    requires s0.stack[11] == 0x3b7

    requires s0.stack[14] == 0x182

    requires s0.stack[16] == 0x16a

    requires s0.stack[20] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x808;
      assert s1.Peek(11) == 0x3b7;
      assert s1.Peek(14) == 0x182;
      assert s1.Peek(16) == 0x16a;
      assert s1.Peek(20) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s8, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 135
    * Starting at 0x808
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x808 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x3b7

    requires s0.stack[9] == 0x182

    requires s0.stack[11] == 0x16a

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3b7;
      assert s1.Peek(9) == 0x182;
      assert s1.Peek(11) == 0x16a;
      assert s1.Peek(15) == 0xb6;
      var s2 := Add(s1);
      var s3 := Push1(s2, 0x28);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Swap4(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s11, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 72
    * Starting at 0x3b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x16a

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x16a;
      assert s1.Peek(9) == 0xb6;
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
      assert s11.Peek(7) == 0x182;
      assert s11.Peek(9) == 0x16a;
      assert s11.Peek(13) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Swap1(s12);
      var s14 := Dup3(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push3(s16, 0x461bcd);
      var s18 := Push1(s17, 0xe5);
      var s19 := Shl(s18);
      var s20 := Dup3(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0x182;
      assert s21.Peek(6) == 0x16a;
      assert s21.Peek(10) == 0xb6;
      var s22 := Push2(s21, 0x03dd);
      var s23 := Swap2(s22);
      var s24 := Push1(s23, 0x04);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x0814);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s27, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 136
    * Starting at 0x814
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x814 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x3dd

    requires s0.stack[5] == 0x182

    requires s0.stack[7] == 0x16a

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3dd;
      assert s1.Peek(5) == 0x182;
      assert s1.Peek(7) == 0x16a;
      assert s1.Peek(11) == 0xb6;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup3(s5);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x3dd;
      assert s11.Peek(9) == 0x182;
      assert s11.Peek(11) == 0x16a;
      assert s11.Peek(15) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0833);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0781);
      assert s21.Peek(0) == 0x781;
      assert s21.Peek(4) == 0x833;
      assert s21.Peek(9) == 0x3dd;
      assert s21.Peek(12) == 0x182;
      assert s21.Peek(14) == 0x16a;
      assert s21.Peek(18) == 0xb6;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s358(s22, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 129
    * Starting at 0x781
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x781 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x833

    requires s0.stack[8] == 0x3dd

    requires s0.stack[11] == 0x182

    requires s0.stack[13] == 0x16a

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x833;
      assert s1.Peek(8) == 0x3dd;
      assert s1.Peek(11) == 0x182;
      assert s1.Peek(13) == 0x16a;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s359(s2, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 130
    * Starting at 0x784
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x784 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x833

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x833;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x079c);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s361(s7, gas - 1)
      else
        ExecuteFromCFGNode_s360(s7, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 131
    * Starting at 0x78d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x833

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x833;
      assert s1.Peek(10) == 0x3dd;
      assert s1.Peek(13) == 0x182;
      assert s1.Peek(15) == 0x16a;
      assert s1.Peek(19) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0784);
      assert s11.Peek(0) == 0x784;
      assert s11.Peek(5) == 0x833;
      assert s11.Peek(10) == 0x3dd;
      assert s11.Peek(13) == 0x182;
      assert s11.Peek(15) == 0x16a;
      assert s11.Peek(19) == 0xb6;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s359(s12, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 132
    * Starting at 0x79c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x833

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x182

    requires s0.stack[14] == 0x16a

    requires s0.stack[18] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x833;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(12) == 0x182;
      assert s1.Peek(14) == 0x16a;
      assert s1.Peek(18) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s8, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 137
    * Starting at 0x833
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x833 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x3dd

    requires s0.stack[7] == 0x182

    requires s0.stack[9] == 0x16a

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3dd;
      assert s1.Peek(7) == 0x182;
      assert s1.Peek(9) == 0x16a;
      assert s1.Peek(13) == 0xb6;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Not(s4);
      var s6 := And(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x3dd;
      assert s11.Peek(7) == 0x182;
      assert s11.Peek(9) == 0x16a;
      assert s11.Peek(13) == 0xb6;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s363(s17, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 73
    * Starting at 0x3dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x182

    requires s0.stack[5] == 0x16a

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x182;
      assert s1.Peek(5) == 0x16a;
      assert s1.Peek(9) == 0xb6;
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

  /** Node 364
    * Segment Id for this node is: 74
    * Starting at 0x3e6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x182

    requires s0.stack[4] == 0x16a

    requires s0.stack[8] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x182;
      assert s1.Peek(4) == 0x16a;
      assert s1.Peek(8) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s4, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 39
    * Starting at 0x182
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x182 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x16a

    requires s0.stack[5] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x16a;
      assert s1.Peek(5) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s366(s3, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 36
    * Starting at 0x16a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb6;
      var s2 := Push2(s1, 0x0174);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x022a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s367(s6, gas - 1)
  }

  /** Node 367
    * Segment Id for this node is: 53
    * Starting at 0x22a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x174

    requires s0.stack[6] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x174;
      assert s1.Peek(6) == 0xb6;
      var s2 := Push2(s1, 0x024b);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0236);
      var s5 := Push2(s4, 0x0357);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s6, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[0] == 0x236

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x174

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x236;
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x174;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s369(s4, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 54
    * Starting at 0x236
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x174

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x174;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup6(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(3) == 0x24b;
      assert s11.Peek(6) == 0x174;
      assert s11.Peek(10) == 0xb6;
      var s12 := Swap1(s11);
      var s13 := Keccak256(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x03ea);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s370(s16, gas - 1)
  }

  /** Node 370
    * Segment Id for this node is: 75
    * Starting at 0x3ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x24b

    requires s0.stack[5] == 0x174

    requires s0.stack[9] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(5) == 0x174;
      assert s1.Peek(9) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0191);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup5(s9);
      var s11 := And(s10);
      assert s11.Peek(2) == 0x191;
      assert s11.Peek(6) == 0x24b;
      assert s11.Peek(9) == 0x174;
      assert s11.Peek(13) == 0xb6;
      var s12 := Push2(s11, 0x05a3);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s13, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 100
    * Starting at 0x5a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x191

    requires s0.stack[6] == 0x24b

    requires s0.stack[9] == 0x174

    requires s0.stack[13] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(9) == 0x174;
      assert s1.Peek(13) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05af);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x062d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s7, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 108
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x5af

    requires s0.stack[6] == 0x191

    requires s0.stack[10] == 0x24b

    requires s0.stack[13] == 0x174

    requires s0.stack[17] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5af;
      assert s1.Peek(6) == 0x191;
      assert s1.Peek(10) == 0x24b;
      assert s1.Peek(13) == 0x174;
      assert s1.Peek(17) == 0xb6;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(3) == 0x5af;
      assert s11.Peek(7) == 0x191;
      assert s11.Peek(11) == 0x24b;
      assert s11.Peek(14) == 0x174;
      assert s11.Peek(18) == 0xb6;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := Swap1(s13);
      var s15 := Keccak256(s14);
      var s16 := SLoad(s15);
      var s17 := IsZero(s16);
      var s18 := IsZero(s17);
      var s19 := Swap1(s18);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s20, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 101
    * Starting at 0x5af
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x191

    requires s0.stack[8] == 0x24b

    requires s0.stack[11] == 0x174

    requires s0.stack[15] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x191;
      assert s1.Peek(8) == 0x24b;
      assert s1.Peek(11) == 0x174;
      assert s1.Peek(15) == 0xb6;
      var s2 := Push2(s1, 0x0152);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s377(s3, gas - 1)
      else
        ExecuteFromCFGNode_s374(s3, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 102
    * Starting at 0x5b4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x24b

    requires s0.stack[10] == 0x174

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(2) == 0x191;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(9) == 0x174;
      assert s1.Peek(13) == 0xb6;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Dup5(s7);
      var s9 := SStore(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup5(s10);
      assert s11.Peek(6) == 0x191;
      assert s11.Peek(10) == 0x24b;
      assert s11.Peek(13) == 0x174;
      assert s11.Peek(17) == 0xb6;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Keccak256(s16);
      var s18 := Swap1(s17);
      var s19 := Swap4(s18);
      var s20 := Add(s19);
      var s21 := Dup5(s20);
      assert s21.Peek(7) == 0x191;
      assert s21.Peek(11) == 0x24b;
      assert s21.Peek(14) == 0x174;
      assert s21.Peek(18) == 0xb6;
      var s22 := Swap1(s21);
      var s23 := SStore(s22);
      var s24 := Dup5(s23);
      var s25 := SLoad(s24);
      var s26 := Swap4(s25);
      var s27 := Dup2(s26);
      var s28 := MStore(s27);
      var s29 := Swap4(s28);
      var s30 := Dup2(s29);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0x191;
      assert s31.Peek(9) == 0x24b;
      assert s31.Peek(12) == 0x174;
      assert s31.Peek(16) == 0xb6;
      var s32 := Swap1(s31);
      var s33 := Swap2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := Swap1(s35);
      var s37 := Swap3(s36);
      var s38 := Keccak256(s37);
      var s39 := SStore(s38);
      var s40 := Swap1(s39);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s41, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 41
    * Starting at 0x191
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x191 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x24b

    requires s0.stack[7] == 0x174

    requires s0.stack[11] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x24b;
      assert s1.Peek(7) == 0x174;
      assert s1.Peek(11) == 0xb6;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s376(s7, gas - 1)
  }

  /** Node 376
    * Segment Id for this node is: 55
    * Starting at 0x24b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x174

    requires s0.stack[7] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x174;
      assert s1.Peek(7) == 0xb6;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Caller(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(5) == 0x174;
      assert s11.Peek(9) == 0xb6;
      var s12 := Dup4(s11);
      var s13 := And(s12);
      var s14 := Swap1(s13);
      var s15 := Dup5(s14);
      var s16 := Swap1(s15);
      var s17 := Push32(s16, 0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d);
      var s18 := Swap1(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Swap1(s19);
      var s21 := Log4(s20);
      assert s21.Peek(2) == 0x174;
      assert s21.Peek(6) == 0xb6;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s24, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 33
    * Starting at 0x152
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x152 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x191

    requires s0.stack[7] == 0x24b

    requires s0.stack[10] == 0x174

    requires s0.stack[14] == 0xb6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x191;
      assert s1.Peek(7) == 0x24b;
      assert s1.Peek(10) == 0x174;
      assert s1.Peek(14) == 0xb6;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s6, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0090);
      var s3 := Push2(s2, 0x008b);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x070a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s379(s7, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 118
    * Starting at 0x70a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x8b

    requires s0.stack[3] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8b;
      assert s1.Peek(3) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x071c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s381(s10, gas - 1)
      else
        ExecuteFromCFGNode_s380(s10, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 119
    * Starting at 0x718
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x718 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x8b

    requires s0.stack[4] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x8b;
      assert s1.Peek(5) == 0x90;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 381
    * Segment Id for this node is: 120
    * Starting at 0x71c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x8b

    requires s0.stack[4] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x8b;
      assert s1.Peek(4) == 0x90;
      var s2 := Pop(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s7, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 13
    * Starting at 0x8b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x90;
      var s2 := Push2(s1, 0x0147);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s383(s3, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 32
    * Starting at 0x147
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0152);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0202);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s384(s6, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 50
    * Starting at 0x202
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x202 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x152

    requires s0.stack[4] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x152;
      assert s1.Peek(4) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x020c);
      var s4 := Push2(s3, 0x0357);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s5, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 66
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x20c

    requires s0.stack[3] == 0x152

    requires s0.stack[6] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x20c;
      assert s1.Peek(3) == 0x152;
      assert s1.Peek(6) == 0x90;
      var s2 := Push32(s1, 0xd3889cc5458b268d0544e5534672df1296288ca3f93cbd39bd6f497a5c622811);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s4, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 51
    * Starting at 0x20c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x152

    requires s0.stack[6] == 0x90

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x152;
      assert s1.Peek(6) == 0x90;
      var s2 := Push1(s1, 0x00);
      var s3 := Swap3(s2);
      var s4 := Dup4(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x152;
      assert s11.Peek(4) == 0x90;
      var s12 := Push1(s11, 0x02);
      var s13 := Add(s12);
      var s14 := SLoad(s13);
      var s15 := Swap1(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s16, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 11
    * Starting at 0x78
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
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
