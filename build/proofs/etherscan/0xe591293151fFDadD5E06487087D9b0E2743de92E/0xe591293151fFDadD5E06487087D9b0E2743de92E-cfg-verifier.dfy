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
      var s4 := CallDataSize(s3);
      var s5 := Push2(s4, 0x0013);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s216(s6, gas - 1)
      else
        ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0xa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0011);
      assert s1.Peek(0) == 0x11;
      var s2 := Push2(s1, 0x0017);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s3, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 4
    * Starting at 0x17
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11;
      var s2 := Push2(s1, 0x001f);
      var s3 := Push2(s2, 0x02a1);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s3(s4, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 22
    * Starting at 0x2a1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1f

    requires s0.stack[1] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1f;
      assert s1.Peek(1) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s4(s3, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 23
    * Starting at 0x2c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1f

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1f;
      assert s1.Peek(3) == 0x11;
      var s2 := SLoad(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s5(s8, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x1f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[1] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x11;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Caller(s3);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0297);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s206(s7, gas - 1)
      else
        ExecuteFromCFGNode_s6(s7, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x60);
      assert s1.Peek(1) == 0x11;
      var s2 := Push32(s1, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := CallDataLoad(s3);
      var s5 := And(s4);
      var s6 := Push32(s5, 0xc9a6301a00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x0098);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s10, gas - 1)
      else
        ExecuteFromCFGNode_s7(s10, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x8a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0091);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push2(s1, 0x02e1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s3, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 24
    * Starting at 0x2e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x91

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x02eb);
      var s4 := Push2(s3, 0x0420);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 44
    * Starting at 0x420
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x2eb

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2eb;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x029f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 45
    * Starting at 0x427
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x427 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x2eb

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(1) == 0x2eb;
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 11
    * Segment Id for this node is: 21
    * Starting at 0x29f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x2eb

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2eb;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s2, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 25
    * Starting at 0x2eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x91

    requires s0.stack[4] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x91;
      assert s1.Peek(4) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02fa);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x08d7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s9, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 89
    * Starting at 0x8d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x2fa

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fa;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x08e7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s9, gas - 1)
      else
        ExecuteFromCFGNode_s14(s9, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 90
    * Starting at 0x8e3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fa

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x2fa;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 15
    * Segment Id for this node is: 91
    * Starting at 0x8e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fa

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fa;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup7(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08f4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s7, gas - 1)
      else
        ExecuteFromCFGNode_s16(s7, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 92
    * Starting at 0x8f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fa

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x2fa;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 17
    * Segment Id for this node is: 93
    * Starting at 0x8f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fa

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fa;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap4(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Sub(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(1) == 0x2fa;
      assert s11.Peek(6) == 0x91;
      assert s11.Peek(9) == 0x11;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s13, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 26
    * Starting at 0x2fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x91

    requires s0.stack[7] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x91;
      assert s1.Peek(7) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0307);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x092a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s9, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 97
    * Starting at 0x92a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x307

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x307;
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x093c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s21(s10, gas - 1)
      else
        ExecuteFromCFGNode_s20(s10, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 98
    * Starting at 0x938
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x307

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 21
    * Segment Id for this node is: 99
    * Starting at 0x93c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x307

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x307;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push2(s1, 0x0560);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0901);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s5, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 94
    * Starting at 0x901
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x901 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x560

    requires s0.stack[5] == 0x307

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x560;
      assert s1.Peek(5) == 0x307;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0925);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s10, gas - 1)
      else
        ExecuteFromCFGNode_s23(s10, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 95
    * Starting at 0x921
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x921 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x560

    requires s0.stack[6] == 0x307

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x560;
      assert s1.Peek(7) == 0x307;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 96
    * Starting at 0x925
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x925 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x560

    requires s0.stack[6] == 0x307

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x560;
      assert s1.Peek(6) == 0x307;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s5, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 64
    * Starting at 0x560
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x560 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x307

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x307;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s7, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 27
    * Starting at 0x307
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x91

    requires s0.stack[6] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0324);
      var s5 := Dup2(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x324;
      assert s11.Peek(7) == 0x91;
      assert s11.Peek(10) == 0x11;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Pop(s16);
      var s18 := Push1(s17, 0x00);
      var s19 := Push2(s18, 0x042b);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s20, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 46
    * Starting at 0x42b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push2(s1, 0x0434);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x04ee);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s5, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 61
    * Starting at 0x4ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x434

    requires s0.stack[5] == 0x324

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x434;
      assert s1.Peek(5) == 0x324;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Push2(s1, 0x04f7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s5, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 70
    * Starting at 0x69b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x4f7

    requires s0.stack[3] == 0x434

    requires s0.stack[7] == 0x324

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4f7;
      assert s1.Peek(3) == 0x434;
      assert s1.Peek(7) == 0x324;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := ExtCodeSize(s4);
      var s6 := Push2(s5, 0x073f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s32(s7, gas - 1)
      else
        ExecuteFromCFGNode_s30(s7, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 71
    * Starting at 0x6b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x4f7

    requires s0.stack[3] == 0x434

    requires s0.stack[7] == 0x324

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x4f7;
      assert s1.Peek(4) == 0x434;
      assert s1.Peek(8) == 0x324;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x2d);
      assert s11.Peek(3) == 0x4f7;
      assert s11.Peek(5) == 0x434;
      assert s11.Peek(9) == 0x324;
      assert s11.Peek(12) == 0x91;
      assert s11.Peek(15) == 0x11;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x455243313936373a206e657720696d706c656d656e746174696f6e206973206e);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x6f74206120636f6e747261637400000000000000000000000000000000000000);
      assert s21.Peek(3) == 0x4f7;
      assert s21.Peek(5) == 0x434;
      assert s21.Peek(9) == 0x324;
      assert s21.Peek(12) == 0x91;
      assert s21.Peek(15) == 0x11;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x0286);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s29, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x4f7

    requires s0.stack[4] == 0x434

    requires s0.stack[8] == 0x324

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4f7;
      assert s1.Peek(4) == 0x434;
      assert s1.Peek(8) == 0x324;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
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

  /** Node 32
    * Segment Id for this node is: 72
    * Starting at 0x73f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x4f7

    requires s0.stack[3] == 0x434

    requires s0.stack[7] == 0x324

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4f7;
      assert s1.Peek(3) == 0x434;
      assert s1.Peek(7) == 0x324;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x062d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s5, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 68
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x4f7

    requires s0.stack[5] == 0x434

    requires s0.stack[9] == 0x324

    requires s0.stack[12] == 0x91

    requires s0.stack[15] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f7;
      assert s1.Peek(5) == 0x434;
      assert s1.Peek(9) == 0x324;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s5 := And(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(4) == 0x4f7;
      assert s11.Peek(6) == 0x434;
      assert s11.Peek(10) == 0x324;
      assert s11.Peek(13) == 0x91;
      assert s11.Peek(16) == 0x11;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Or(s13);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s18, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 62
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x434

    requires s0.stack[5] == 0x324

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x434;
      assert s1.Peek(5) == 0x324;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Swap1(s6);
      var s8 := Push32(s7, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x434;
      assert s11.Peek(9) == 0x324;
      assert s11.Peek(12) == 0x91;
      assert s11.Peek(15) == 0x11;
      var s12 := Log2(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s14, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 47
    * Starting at 0x434
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0441);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s8, gas - 1)
      else
        ExecuteFromCFGNode_s36(s8, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 48
    * Starting at 0x43f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x324

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s37(s2, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 49
    * Starting at 0x441
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x441 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x324

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x324;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0452);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s4, gas - 1)
      else
        ExecuteFromCFGNode_s38(s4, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 50
    * Starting at 0x447
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x447 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0450);
      assert s1.Peek(0) == 0x450;
      assert s1.Peek(4) == 0x324;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x053b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 63
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x450

    requires s0.stack[6] == 0x324

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x450;
      assert s1.Peek(6) == 0x324;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0560);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x560;
      assert s11.Peek(9) == 0x450;
      assert s11.Peek(13) == 0x324;
      assert s11.Peek(16) == 0x91;
      assert s11.Peek(19) == 0x11;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x27);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0ae6);
      var s20 := Push1(s19, 0x27);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x560;
      assert s21.Peek(10) == 0x450;
      assert s21.Peek(14) == 0x324;
      assert s21.Peek(17) == 0x91;
      assert s21.Peek(20) == 0x11;
      var s22 := CodeCopy(s21);
      var s23 := Push2(s22, 0x0766);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s24, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 73
    * Starting at 0x766
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x766 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x560

    requires s0.stack[7] == 0x450

    requires s0.stack[11] == 0x324

    requires s0.stack[14] == 0x91

    requires s0.stack[17] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x560;
      assert s1.Peek(7) == 0x450;
      assert s1.Peek(11) == 0x324;
      assert s1.Peek(14) == 0x91;
      assert s1.Peek(17) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup1(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup6(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0790);
      assert s11.Peek(0) == 0x790;
      assert s11.Peek(10) == 0x560;
      assert s11.Peek(14) == 0x450;
      assert s11.Peek(18) == 0x324;
      assert s11.Peek(21) == 0x91;
      assert s11.Peek(24) == 0x11;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0a78);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s41(s15, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 119
    * Starting at 0xa78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x790

    requires s0.stack[10] == 0x560

    requires s0.stack[14] == 0x450

    requires s0.stack[18] == 0x324

    requires s0.stack[21] == 0x91

    requires s0.stack[24] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x790;
      assert s1.Peek(10) == 0x560;
      assert s1.Peek(14) == 0x450;
      assert s1.Peek(18) == 0x324;
      assert s1.Peek(21) == 0x91;
      assert s1.Peek(24) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x0a8a);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0a54);
      assert s11.Peek(0) == 0xa54;
      assert s11.Peek(4) == 0xa8a;
      assert s11.Peek(9) == 0x790;
      assert s11.Peek(17) == 0x560;
      assert s11.Peek(21) == 0x450;
      assert s11.Peek(25) == 0x324;
      assert s11.Peek(28) == 0x91;
      assert s11.Peek(31) == 0x11;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s12, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 115
    * Starting at 0xa54
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0xa8a

    requires s0.stack[8] == 0x790

    requires s0.stack[16] == 0x560

    requires s0.stack[20] == 0x450

    requires s0.stack[24] == 0x324

    requires s0.stack[27] == 0x91

    requires s0.stack[30] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8a;
      assert s1.Peek(8) == 0x790;
      assert s1.Peek(16) == 0x560;
      assert s1.Peek(20) == 0x450;
      assert s1.Peek(24) == 0x324;
      assert s1.Peek(27) == 0x91;
      assert s1.Peek(30) == 0x11;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s43(s2, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 116
    * Starting at 0xa57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0xa8a

    requires s0.stack[9] == 0x790

    requires s0.stack[17] == 0x560

    requires s0.stack[21] == 0x450

    requires s0.stack[25] == 0x324

    requires s0.stack[28] == 0x91

    requires s0.stack[31] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa8a;
      assert s1.Peek(9) == 0x790;
      assert s1.Peek(17) == 0x560;
      assert s1.Peek(21) == 0x450;
      assert s1.Peek(25) == 0x324;
      assert s1.Peek(28) == 0x91;
      assert s1.Peek(31) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s7, gas - 1)
      else
        ExecuteFromCFGNode_s44(s7, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 117
    * Starting at 0xa60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0xa8a

    requires s0.stack[9] == 0x790

    requires s0.stack[17] == 0x560

    requires s0.stack[21] == 0x450

    requires s0.stack[25] == 0x324

    requires s0.stack[28] == 0x91

    requires s0.stack[31] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xa8a;
      assert s1.Peek(10) == 0x790;
      assert s1.Peek(18) == 0x560;
      assert s1.Peek(22) == 0x450;
      assert s1.Peek(26) == 0x324;
      assert s1.Peek(29) == 0x91;
      assert s1.Peek(32) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0a57);
      assert s11.Peek(0) == 0xa57;
      assert s11.Peek(5) == 0xa8a;
      assert s11.Peek(10) == 0x790;
      assert s11.Peek(18) == 0x560;
      assert s11.Peek(22) == 0x450;
      assert s11.Peek(26) == 0x324;
      assert s11.Peek(29) == 0x91;
      assert s11.Peek(32) == 0x11;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s12, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 118
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0xa8a

    requires s0.stack[9] == 0x790

    requires s0.stack[17] == 0x560

    requires s0.stack[21] == 0x450

    requires s0.stack[25] == 0x324

    requires s0.stack[28] == 0x91

    requires s0.stack[31] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa8a;
      assert s1.Peek(9) == 0x790;
      assert s1.Peek(17) == 0x560;
      assert s1.Peek(21) == 0x450;
      assert s1.Peek(25) == 0x324;
      assert s1.Peek(28) == 0x91;
      assert s1.Peek(31) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s8, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 120
    * Starting at 0xa8a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[4] == 0x790

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x790;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x324;
      assert s1.Peek(23) == 0x91;
      assert s1.Peek(26) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s10, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 74
    * Starting at 0x790
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x790 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[8] == 0x560

    requires s0.stack[12] == 0x450

    requires s0.stack[16] == 0x324

    requires s0.stack[19] == 0x91

    requires s0.stack[22] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x560;
      assert s1.Peek(12) == 0x450;
      assert s1.Peek(16) == 0x324;
      assert s1.Peek(19) == 0x91;
      assert s1.Peek(22) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Gas(s9);
      var s11 := DelegateCall(s10);
      assert s11.Peek(9) == 0x560;
      assert s11.Peek(13) == 0x450;
      assert s11.Peek(17) == 0x324;
      assert s11.Peek(20) == 0x91;
      assert s11.Peek(23) == 0x11;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x07cb);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s75(s21, gas - 1)
      else
        ExecuteFromCFGNode_s48(s21, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 75
    * Starting at 0x7aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[9] == 0x560

    requires s0.stack[13] == 0x450

    requires s0.stack[17] == 0x324

    requires s0.stack[20] == 0x91

    requires s0.stack[23] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x560;
      assert s1.Peek(14) == 0x450;
      assert s1.Peek(18) == 0x324;
      assert s1.Peek(21) == 0x91;
      assert s1.Peek(24) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x560;
      assert s11.Peek(15) == 0x450;
      assert s11.Peek(19) == 0x324;
      assert s11.Peek(22) == 0x91;
      assert s11.Peek(25) == 0x11;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(13) == 0x560;
      assert s21.Peek(17) == 0x450;
      assert s21.Peek(21) == 0x324;
      assert s21.Peek(24) == 0x91;
      assert s21.Peek(27) == 0x11;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x07d0);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s25, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 77
    * Starting at 0x7d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[9] == 0x560

    requires s0.stack[13] == 0x450

    requires s0.stack[17] == 0x324

    requires s0.stack[20] == 0x91

    requires s0.stack[23] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x560;
      assert s1.Peek(13) == 0x450;
      assert s1.Peek(17) == 0x324;
      assert s1.Peek(20) == 0x91;
      assert s1.Peek(23) == 0x11;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x07e1);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x7e1;
      assert s11.Peek(11) == 0x560;
      assert s11.Peek(15) == 0x450;
      assert s11.Peek(19) == 0x324;
      assert s11.Peek(22) == 0x91;
      assert s11.Peek(25) == 0x11;
      var s12 := Push2(s11, 0x07eb);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s13, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 79
    * Starting at 0x7eb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[4] == 0x7e1

    requires s0.stack[11] == 0x560

    requires s0.stack[15] == 0x450

    requires s0.stack[19] == 0x324

    requires s0.stack[22] == 0x91

    requires s0.stack[25] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7e1;
      assert s1.Peek(11) == 0x560;
      assert s1.Peek(15) == 0x450;
      assert s1.Peek(19) == 0x324;
      assert s1.Peek(22) == 0x91;
      assert s1.Peek(25) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0881);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s6, gas - 1)
      else
        ExecuteFromCFGNode_s51(s6, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 80
    * Starting at 0x7f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x324;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x087a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s6, gas - 1)
      else
        ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 81
    * Starting at 0x7fd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push20(s0, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x324;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
      var s2 := Dup6(s1);
      var s3 := And(s2);
      var s4 := ExtCodeSize(s3);
      var s5 := Push2(s4, 0x087a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s6, gas - 1)
      else
        ExecuteFromCFGNode_s53(s6, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 82
    * Starting at 0x819
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x819 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x324;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x1d);
      assert s11.Peek(7) == 0x7e1;
      assert s11.Peek(14) == 0x560;
      assert s11.Peek(18) == 0x450;
      assert s11.Peek(22) == 0x324;
      assert s11.Peek(25) == 0x91;
      assert s11.Peek(28) == 0x11;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(7) == 0x7e1;
      assert s21.Peek(14) == 0x560;
      assert s21.Peek(18) == 0x450;
      assert s21.Peek(22) == 0x324;
      assert s21.Peek(25) == 0x91;
      assert s21.Peek(28) == 0x11;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0286);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s24, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[6] == 0x7e1

    requires s0.stack[13] == 0x560

    requires s0.stack[17] == 0x450

    requires s0.stack[21] == 0x324

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x324;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
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

  /** Node 55
    * Segment Id for this node is: 83
    * Starting at 0x87a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7e1;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x324;
      assert s1.Peek(23) == 0x91;
      assert s1.Peek(26) == 0x11;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x088b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s5, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 85
    * Starting at 0x88b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7e1;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x324;
      assert s1.Peek(23) == 0x91;
      assert s1.Peek(26) == 0x11;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s8, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 78
    * Starting at 0x7e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x560

    requires s0.stack[11] == 0x450

    requires s0.stack[15] == 0x324

    requires s0.stack[18] == 0x91

    requires s0.stack[21] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x560;
      assert s1.Peek(11) == 0x450;
      assert s1.Peek(15) == 0x324;
      assert s1.Peek(18) == 0x91;
      assert s1.Peek(21) == 0x11;
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
      ExecuteFromCFGNode_s58(s10, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 64
    * Starting at 0x560
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x560 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x450

    requires s0.stack[8] == 0x324

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x450;
      assert s1.Peek(8) == 0x324;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
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
    * Segment Id for this node is: 51
    * Starting at 0x450
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x324

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x324;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s60(s2, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 52
    * Starting at 0x452
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s5, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 28
    * Starting at 0x324
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup1(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(3) == 0x91;
      assert s11.Peek(6) == 0x11;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Swap1(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s17, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 8
    * Starting at 0x91
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x028f);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s5, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 19
    * Starting at 0x28f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 64
    * Segment Id for this node is: 84
    * Starting at 0x881
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x881 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x324

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7e1;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x324;
      assert s1.Peek(23) == 0x91;
      assert s1.Peek(26) == 0x11;
      var s2 := Push2(s1, 0x088b);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0893);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s6, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 86
    * Starting at 0x893
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x893 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0x88b

    requires s0.stack[8] == 0x7e1

    requires s0.stack[15] == 0x560

    requires s0.stack[19] == 0x450

    requires s0.stack[23] == 0x324

    requires s0.stack[26] == 0x91

    requires s0.stack[29] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x88b;
      assert s1.Peek(8) == 0x7e1;
      assert s1.Peek(15) == 0x560;
      assert s1.Peek(19) == 0x450;
      assert s1.Peek(23) == 0x324;
      assert s1.Peek(26) == 0x91;
      assert s1.Peek(29) == 0x11;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x08a3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s6, gas - 1)
      else
        ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 87
    * Starting at 0x89b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0x88b

    requires s0.stack[8] == 0x7e1

    requires s0.stack[15] == 0x560

    requires s0.stack[19] == 0x450

    requires s0.stack[23] == 0x324

    requires s0.stack[26] == 0x91

    requires s0.stack[29] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x88b;
      assert s1.Peek(9) == 0x7e1;
      assert s1.Peek(16) == 0x560;
      assert s1.Peek(20) == 0x450;
      assert s1.Peek(24) == 0x324;
      assert s1.Peek(27) == 0x91;
      assert s1.Peek(30) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 67
    * Segment Id for this node is: 88
    * Starting at 0x8a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0x88b

    requires s0.stack[8] == 0x7e1

    requires s0.stack[15] == 0x560

    requires s0.stack[19] == 0x450

    requires s0.stack[23] == 0x324

    requires s0.stack[26] == 0x91

    requires s0.stack[29] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x88b;
      assert s1.Peek(8) == 0x7e1;
      assert s1.Peek(15) == 0x560;
      assert s1.Peek(19) == 0x450;
      assert s1.Peek(23) == 0x324;
      assert s1.Peek(26) == 0x91;
      assert s1.Peek(29) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0286);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x286;
      assert s11.Peek(5) == 0x88b;
      assert s11.Peek(11) == 0x7e1;
      assert s11.Peek(18) == 0x560;
      assert s11.Peek(22) == 0x450;
      assert s11.Peek(26) == 0x324;
      assert s11.Peek(29) == 0x91;
      assert s11.Peek(32) == 0x11;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0a94);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s14, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 121
    * Starting at 0xa94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[2] == 0x286

    requires s0.stack[5] == 0x88b

    requires s0.stack[11] == 0x7e1

    requires s0.stack[18] == 0x560

    requires s0.stack[22] == 0x450

    requires s0.stack[26] == 0x324

    requires s0.stack[29] == 0x91

    requires s0.stack[32] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x286;
      assert s1.Peek(5) == 0x88b;
      assert s1.Peek(11) == 0x7e1;
      assert s1.Peek(18) == 0x560;
      assert s1.Peek(22) == 0x450;
      assert s1.Peek(26) == 0x324;
      assert s1.Peek(29) == 0x91;
      assert s1.Peek(32) == 0x11;
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
      assert s11.Peek(6) == 0x286;
      assert s11.Peek(9) == 0x88b;
      assert s11.Peek(15) == 0x7e1;
      assert s11.Peek(22) == 0x560;
      assert s11.Peek(26) == 0x450;
      assert s11.Peek(30) == 0x324;
      assert s11.Peek(33) == 0x91;
      assert s11.Peek(36) == 0x11;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0ab3);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0a54);
      assert s21.Peek(0) == 0xa54;
      assert s21.Peek(4) == 0xab3;
      assert s21.Peek(9) == 0x286;
      assert s21.Peek(12) == 0x88b;
      assert s21.Peek(18) == 0x7e1;
      assert s21.Peek(25) == 0x560;
      assert s21.Peek(29) == 0x450;
      assert s21.Peek(33) == 0x324;
      assert s21.Peek(36) == 0x91;
      assert s21.Peek(39) == 0x11;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s22, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 115
    * Starting at 0xa54
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[3] == 0xab3

    requires s0.stack[8] == 0x286

    requires s0.stack[11] == 0x88b

    requires s0.stack[17] == 0x7e1

    requires s0.stack[24] == 0x560

    requires s0.stack[28] == 0x450

    requires s0.stack[32] == 0x324

    requires s0.stack[35] == 0x91

    requires s0.stack[38] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab3;
      assert s1.Peek(8) == 0x286;
      assert s1.Peek(11) == 0x88b;
      assert s1.Peek(17) == 0x7e1;
      assert s1.Peek(24) == 0x560;
      assert s1.Peek(28) == 0x450;
      assert s1.Peek(32) == 0x324;
      assert s1.Peek(35) == 0x91;
      assert s1.Peek(38) == 0x11;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s70(s2, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 116
    * Starting at 0xa57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 40

    requires s0.stack[4] == 0xab3

    requires s0.stack[9] == 0x286

    requires s0.stack[12] == 0x88b

    requires s0.stack[18] == 0x7e1

    requires s0.stack[25] == 0x560

    requires s0.stack[29] == 0x450

    requires s0.stack[33] == 0x324

    requires s0.stack[36] == 0x91

    requires s0.stack[39] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xab3;
      assert s1.Peek(9) == 0x286;
      assert s1.Peek(12) == 0x88b;
      assert s1.Peek(18) == 0x7e1;
      assert s1.Peek(25) == 0x560;
      assert s1.Peek(29) == 0x450;
      assert s1.Peek(33) == 0x324;
      assert s1.Peek(36) == 0x91;
      assert s1.Peek(39) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s7, gas - 1)
      else
        ExecuteFromCFGNode_s71(s7, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 117
    * Starting at 0xa60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 40

    requires s0.stack[4] == 0xab3

    requires s0.stack[9] == 0x286

    requires s0.stack[12] == 0x88b

    requires s0.stack[18] == 0x7e1

    requires s0.stack[25] == 0x560

    requires s0.stack[29] == 0x450

    requires s0.stack[33] == 0x324

    requires s0.stack[36] == 0x91

    requires s0.stack[39] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xab3;
      assert s1.Peek(10) == 0x286;
      assert s1.Peek(13) == 0x88b;
      assert s1.Peek(19) == 0x7e1;
      assert s1.Peek(26) == 0x560;
      assert s1.Peek(30) == 0x450;
      assert s1.Peek(34) == 0x324;
      assert s1.Peek(37) == 0x91;
      assert s1.Peek(40) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0a57);
      assert s11.Peek(0) == 0xa57;
      assert s11.Peek(5) == 0xab3;
      assert s11.Peek(10) == 0x286;
      assert s11.Peek(13) == 0x88b;
      assert s11.Peek(19) == 0x7e1;
      assert s11.Peek(26) == 0x560;
      assert s11.Peek(30) == 0x450;
      assert s11.Peek(34) == 0x324;
      assert s11.Peek(37) == 0x91;
      assert s11.Peek(40) == 0x11;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s12, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 118
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 40

    requires s0.stack[4] == 0xab3

    requires s0.stack[9] == 0x286

    requires s0.stack[12] == 0x88b

    requires s0.stack[18] == 0x7e1

    requires s0.stack[25] == 0x560

    requires s0.stack[29] == 0x450

    requires s0.stack[33] == 0x324

    requires s0.stack[36] == 0x91

    requires s0.stack[39] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xab3;
      assert s1.Peek(9) == 0x286;
      assert s1.Peek(12) == 0x88b;
      assert s1.Peek(18) == 0x7e1;
      assert s1.Peek(25) == 0x560;
      assert s1.Peek(29) == 0x450;
      assert s1.Peek(33) == 0x324;
      assert s1.Peek(36) == 0x91;
      assert s1.Peek(39) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s8, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 122
    * Starting at 0xab3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 35

    requires s0.stack[4] == 0x286

    requires s0.stack[7] == 0x88b

    requires s0.stack[13] == 0x7e1

    requires s0.stack[20] == 0x560

    requires s0.stack[24] == 0x450

    requires s0.stack[28] == 0x324

    requires s0.stack[31] == 0x91

    requires s0.stack[34] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x286;
      assert s1.Peek(7) == 0x88b;
      assert s1.Peek(13) == 0x7e1;
      assert s1.Peek(20) == 0x560;
      assert s1.Peek(24) == 0x450;
      assert s1.Peek(28) == 0x324;
      assert s1.Peek(31) == 0x91;
      assert s1.Peek(34) == 0x11;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := And(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x286;
      assert s11.Peek(6) == 0x88b;
      assert s11.Peek(12) == 0x7e1;
      assert s11.Peek(19) == 0x560;
      assert s11.Peek(23) == 0x450;
      assert s11.Peek(27) == 0x324;
      assert s11.Peek(30) == 0x91;
      assert s11.Peek(33) == 0x11;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s16, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[3] == 0x88b

    requires s0.stack[9] == 0x7e1

    requires s0.stack[16] == 0x560

    requires s0.stack[20] == 0x450

    requires s0.stack[24] == 0x324

    requires s0.stack[27] == 0x91

    requires s0.stack[30] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x88b;
      assert s1.Peek(9) == 0x7e1;
      assert s1.Peek(16) == 0x560;
      assert s1.Peek(20) == 0x450;
      assert s1.Peek(24) == 0x324;
      assert s1.Peek(27) == 0x91;
      assert s1.Peek(30) == 0x11;
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

  /** Node 75
    * Segment Id for this node is: 76
    * Starting at 0x7cb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[9] == 0x560

    requires s0.stack[13] == 0x450

    requires s0.stack[17] == 0x324

    requires s0.stack[20] == 0x91

    requires s0.stack[23] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x560;
      assert s1.Peek(13) == 0x450;
      assert s1.Peek(17) == 0x324;
      assert s1.Peek(20) == 0x91;
      assert s1.Peek(23) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s49(s4, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 9
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11;
      var s2 := Push32(s1, 0xb0e10d7a00000000000000000000000000000000000000000000000000000000);
      var s3 := Push32(s2, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x00e9);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s8, gas - 1)
      else
        ExecuteFromCFGNode_s77(s8, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 10
    * Starting at 0xe2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0091);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push2(s1, 0x0338);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s3, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 29
    * Starting at 0x338
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x338 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x91

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup1(s3);
      var s5 := Push2(s4, 0x034a);
      var s6 := CallDataSize(s5);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup2(s7);
      var s9 := Dup5(s8);
      var s10 := Push2(s9, 0x08d7);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s11, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 89
    * Starting at 0x8d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x34a

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x34a;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x08e7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s9, gas - 1)
      else
        ExecuteFromCFGNode_s80(s9, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 90
    * Starting at 0x8e3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x34a

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x34a;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 81
    * Segment Id for this node is: 91
    * Starting at 0x8e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x34a

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x34a;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup7(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08f4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s7, gas - 1)
      else
        ExecuteFromCFGNode_s82(s7, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 92
    * Starting at 0x8f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x34a

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x34a;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 83
    * Segment Id for this node is: 93
    * Starting at 0x8f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x34a

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x34a;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap4(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Sub(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(1) == 0x34a;
      assert s11.Peek(7) == 0x91;
      assert s11.Peek(10) == 0x11;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s13, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 30
    * Starting at 0x34a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x0357);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0974);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s9, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 101
    * Starting at 0x974
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x974 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x357

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x357;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0987);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s11, gas - 1)
      else
        ExecuteFromCFGNode_s86(s11, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 102
    * Starting at 0x983
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x357

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x357;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 87
    * Segment Id for this node is: 103
    * Starting at 0x987
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x987 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x357

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x357;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Push2(s1, 0x0990);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0901);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s5, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 94
    * Starting at 0x901
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x901 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x990

    requires s0.stack[6] == 0x357

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x990;
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0925);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s10, gas - 1)
      else
        ExecuteFromCFGNode_s89(s10, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 95
    * Starting at 0x921
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x921 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x990

    requires s0.stack[7] == 0x357

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x990;
      assert s1.Peek(8) == 0x357;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 90
    * Segment Id for this node is: 96
    * Starting at 0x925
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x925 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x990

    requires s0.stack[7] == 0x357

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x990;
      assert s1.Peek(7) == 0x357;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s5, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 104
    * Starting at 0x990
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x990 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x357

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x357;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(7) == 0x357;
      assert s11.Peek(11) == 0x91;
      assert s11.Peek(14) == 0x11;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x09ad);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s14, gas - 1)
      else
        ExecuteFromCFGNode_s92(s14, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 105
    * Starting at 0x9a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x357

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x357;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 93
    * Segment Id for this node is: 106
    * Starting at 0x9ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x357

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup6(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := SLt(s10);
      assert s11.Peek(7) == 0x357;
      assert s11.Peek(11) == 0x91;
      assert s11.Peek(14) == 0x11;
      var s12 := Push2(s11, 0x09c1);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s13, gas - 1)
      else
        ExecuteFromCFGNode_s94(s13, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 107
    * Starting at 0x9bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x357

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x357;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 95
    * Segment Id for this node is: 108
    * Starting at 0x9c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0x357

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x357;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09d3);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s9, gas - 1)
      else
        ExecuteFromCFGNode_s96(s9, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 109
    * Starting at 0x9cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x357

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x09d3);
      assert s1.Peek(0) == 0x9d3;
      assert s1.Peek(8) == 0x357;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
      var s2 := Push2(s1, 0x0945);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s3, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 100
    * Starting at 0x945
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x945 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x9d3

    requires s0.stack[8] == 0x357

    requires s0.stack[12] == 0x91

    requires s0.stack[15] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x9d3;
      assert s1.Peek(8) == 0x357;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
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

  /** Node 98
    * Segment Id for this node is: 110
    * Starting at 0x9d3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x357

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x357;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(11) == 0x357;
      assert s11.Peek(15) == 0x91;
      assert s11.Peek(18) == 0x11;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup4(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(12) == 0x357;
      assert s21.Peek(16) == 0x91;
      assert s21.Peek(19) == 0x11;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0a19);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s26, gas - 1)
      else
        ExecuteFromCFGNode_s99(s26, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 111
    * Starting at 0xa12
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[9] == 0x357

    requires s0.stack[13] == 0x91

    requires s0.stack[16] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0a19);
      assert s1.Peek(0) == 0xa19;
      assert s1.Peek(10) == 0x357;
      assert s1.Peek(14) == 0x91;
      assert s1.Peek(17) == 0x11;
      var s2 := Push2(s1, 0x0945);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s3, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 100
    * Starting at 0x945
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x945 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0xa19

    requires s0.stack[10] == 0x357

    requires s0.stack[14] == 0x91

    requires s0.stack[17] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa19;
      assert s1.Peek(10) == 0x357;
      assert s1.Peek(14) == 0x91;
      assert s1.Peek(17) == 0x11;
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

  /** Node 101
    * Segment Id for this node is: 112
    * Starting at 0xa19
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa19 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[9] == 0x357

    requires s0.stack[13] == 0x91

    requires s0.stack[16] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x357;
      assert s1.Peek(13) == 0x91;
      assert s1.Peek(16) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup3(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup9(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup5(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(13) == 0x357;
      assert s11.Peek(17) == 0x91;
      assert s11.Peek(20) == 0x11;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x0a32);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s17, gas - 1)
      else
        ExecuteFromCFGNode_s102(s17, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 113
    * Starting at 0xa2e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[9] == 0x357

    requires s0.stack[13] == 0x91

    requires s0.stack[16] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(10) == 0x357;
      assert s1.Peek(14) == 0x91;
      assert s1.Peek(17) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 103
    * Segment Id for this node is: 114
    * Starting at 0xa32
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa32 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[9] == 0x357

    requires s0.stack[13] == 0x91

    requires s0.stack[16] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x357;
      assert s1.Peek(13) == 0x91;
      assert s1.Peek(16) == 0x11;
      var s2 := Dup3(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup7(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(11) == 0x357;
      assert s11.Peek(15) == 0x91;
      assert s11.Peek(18) == 0x11;
      var s12 := Dup5(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap6(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(7) == 0x357;
      assert s21.Peek(11) == 0x91;
      assert s21.Peek(14) == 0x11;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Swap3(s24);
      var s26 := Pop(s25);
      var s27 := Swap3(s26);
      var s28 := Swap1(s27);
      var s29 := Pop(s28);
      var s30 := Jump(s29);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s30, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 31
    * Starting at 0x357
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x357 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      var s6 := Push2(s5, 0x0367);
      var s7 := Dup3(s6);
      var s8 := Dup3(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push2(s9, 0x042b);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s11, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 46
    * Starting at 0x42b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x367

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x367;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Push2(s1, 0x0434);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x04ee);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s5, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 61
    * Starting at 0x4ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x434

    requires s0.stack[5] == 0x367

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x434;
      assert s1.Peek(5) == 0x367;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Push2(s1, 0x04f7);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x069b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s5, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 70
    * Starting at 0x69b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x69b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x4f7

    requires s0.stack[3] == 0x434

    requires s0.stack[7] == 0x367

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4f7;
      assert s1.Peek(3) == 0x434;
      assert s1.Peek(7) == 0x367;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := ExtCodeSize(s4);
      var s6 := Push2(s5, 0x073f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s7, gas - 1)
      else
        ExecuteFromCFGNode_s108(s7, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 71
    * Starting at 0x6b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x4f7

    requires s0.stack[3] == 0x434

    requires s0.stack[7] == 0x367

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x4f7;
      assert s1.Peek(4) == 0x434;
      assert s1.Peek(8) == 0x367;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x2d);
      assert s11.Peek(3) == 0x4f7;
      assert s11.Peek(5) == 0x434;
      assert s11.Peek(9) == 0x367;
      assert s11.Peek(13) == 0x91;
      assert s11.Peek(16) == 0x11;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x455243313936373a206e657720696d706c656d656e746174696f6e206973206e);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x6f74206120636f6e747261637400000000000000000000000000000000000000);
      assert s21.Peek(3) == 0x4f7;
      assert s21.Peek(5) == 0x434;
      assert s21.Peek(9) == 0x367;
      assert s21.Peek(13) == 0x91;
      assert s21.Peek(16) == 0x11;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x0286);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s29, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x4f7

    requires s0.stack[4] == 0x434

    requires s0.stack[8] == 0x367

    requires s0.stack[12] == 0x91

    requires s0.stack[15] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4f7;
      assert s1.Peek(4) == 0x434;
      assert s1.Peek(8) == 0x367;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
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

  /** Node 110
    * Segment Id for this node is: 72
    * Starting at 0x73f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[1] == 0x4f7

    requires s0.stack[3] == 0x434

    requires s0.stack[7] == 0x367

    requires s0.stack[11] == 0x91

    requires s0.stack[14] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4f7;
      assert s1.Peek(3) == 0x434;
      assert s1.Peek(7) == 0x367;
      assert s1.Peek(11) == 0x91;
      assert s1.Peek(14) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x062d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 68
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x4f7

    requires s0.stack[5] == 0x434

    requires s0.stack[9] == 0x367

    requires s0.stack[13] == 0x91

    requires s0.stack[16] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f7;
      assert s1.Peek(5) == 0x434;
      assert s1.Peek(9) == 0x367;
      assert s1.Peek(13) == 0x91;
      assert s1.Peek(16) == 0x11;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s5 := And(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(4) == 0x4f7;
      assert s11.Peek(6) == 0x434;
      assert s11.Peek(10) == 0x367;
      assert s11.Peek(14) == 0x91;
      assert s11.Peek(17) == 0x11;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Or(s13);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s18, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 62
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x434

    requires s0.stack[5] == 0x367

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x434;
      assert s1.Peek(5) == 0x367;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Swap1(s6);
      var s8 := Push32(s7, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x434;
      assert s11.Peek(9) == 0x367;
      assert s11.Peek(13) == 0x91;
      assert s11.Peek(16) == 0x11;
      var s12 := Log2(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 47
    * Starting at 0x434
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x434 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x367

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x367;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x0441);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s8, gas - 1)
      else
        ExecuteFromCFGNode_s114(s8, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 48
    * Starting at 0x43f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x367

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x367;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s115(s2, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 49
    * Starting at 0x441
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x441 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x367

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x367;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0452);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s4, gas - 1)
      else
        ExecuteFromCFGNode_s116(s4, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 50
    * Starting at 0x447
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x447 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x367

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0450);
      assert s1.Peek(0) == 0x450;
      assert s1.Peek(4) == 0x367;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x053b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s5, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 63
    * Starting at 0x53b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x450

    requires s0.stack[6] == 0x367

    requires s0.stack[10] == 0x91

    requires s0.stack[13] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x450;
      assert s1.Peek(6) == 0x367;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0560);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x560;
      assert s11.Peek(9) == 0x450;
      assert s11.Peek(13) == 0x367;
      assert s11.Peek(17) == 0x91;
      assert s11.Peek(20) == 0x11;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x27);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0ae6);
      var s20 := Push1(s19, 0x27);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x560;
      assert s21.Peek(10) == 0x450;
      assert s21.Peek(14) == 0x367;
      assert s21.Peek(18) == 0x91;
      assert s21.Peek(21) == 0x11;
      var s22 := CodeCopy(s21);
      var s23 := Push2(s22, 0x0766);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s24, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 73
    * Starting at 0x766
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x766 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x560

    requires s0.stack[7] == 0x450

    requires s0.stack[11] == 0x367

    requires s0.stack[15] == 0x91

    requires s0.stack[18] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x560;
      assert s1.Peek(7) == 0x450;
      assert s1.Peek(11) == 0x367;
      assert s1.Peek(15) == 0x91;
      assert s1.Peek(18) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup1(s3);
      var s5 := Dup6(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := And(s6);
      var s8 := Dup6(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Push2(s10, 0x0790);
      assert s11.Peek(0) == 0x790;
      assert s11.Peek(10) == 0x560;
      assert s11.Peek(14) == 0x450;
      assert s11.Peek(18) == 0x367;
      assert s11.Peek(22) == 0x91;
      assert s11.Peek(25) == 0x11;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x0a78);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s15, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 119
    * Starting at 0xa78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[2] == 0x790

    requires s0.stack[10] == 0x560

    requires s0.stack[14] == 0x450

    requires s0.stack[18] == 0x367

    requires s0.stack[22] == 0x91

    requires s0.stack[25] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x790;
      assert s1.Peek(10) == 0x560;
      assert s1.Peek(14) == 0x450;
      assert s1.Peek(18) == 0x367;
      assert s1.Peek(22) == 0x91;
      assert s1.Peek(25) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x0a8a);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0a54);
      assert s11.Peek(0) == 0xa54;
      assert s11.Peek(4) == 0xa8a;
      assert s11.Peek(9) == 0x790;
      assert s11.Peek(17) == 0x560;
      assert s11.Peek(21) == 0x450;
      assert s11.Peek(25) == 0x367;
      assert s11.Peek(29) == 0x91;
      assert s11.Peek(32) == 0x11;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s12, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 115
    * Starting at 0xa54
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0xa8a

    requires s0.stack[8] == 0x790

    requires s0.stack[16] == 0x560

    requires s0.stack[20] == 0x450

    requires s0.stack[24] == 0x367

    requires s0.stack[28] == 0x91

    requires s0.stack[31] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa8a;
      assert s1.Peek(8) == 0x790;
      assert s1.Peek(16) == 0x560;
      assert s1.Peek(20) == 0x450;
      assert s1.Peek(24) == 0x367;
      assert s1.Peek(28) == 0x91;
      assert s1.Peek(31) == 0x11;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s2, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 116
    * Starting at 0xa57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[4] == 0xa8a

    requires s0.stack[9] == 0x790

    requires s0.stack[17] == 0x560

    requires s0.stack[21] == 0x450

    requires s0.stack[25] == 0x367

    requires s0.stack[29] == 0x91

    requires s0.stack[32] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa8a;
      assert s1.Peek(9) == 0x790;
      assert s1.Peek(17) == 0x560;
      assert s1.Peek(21) == 0x450;
      assert s1.Peek(25) == 0x367;
      assert s1.Peek(29) == 0x91;
      assert s1.Peek(32) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s7, gas - 1)
      else
        ExecuteFromCFGNode_s122(s7, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 117
    * Starting at 0xa60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[4] == 0xa8a

    requires s0.stack[9] == 0x790

    requires s0.stack[17] == 0x560

    requires s0.stack[21] == 0x450

    requires s0.stack[25] == 0x367

    requires s0.stack[29] == 0x91

    requires s0.stack[32] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xa8a;
      assert s1.Peek(10) == 0x790;
      assert s1.Peek(18) == 0x560;
      assert s1.Peek(22) == 0x450;
      assert s1.Peek(26) == 0x367;
      assert s1.Peek(30) == 0x91;
      assert s1.Peek(33) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0a57);
      assert s11.Peek(0) == 0xa57;
      assert s11.Peek(5) == 0xa8a;
      assert s11.Peek(10) == 0x790;
      assert s11.Peek(18) == 0x560;
      assert s11.Peek(22) == 0x450;
      assert s11.Peek(26) == 0x367;
      assert s11.Peek(30) == 0x91;
      assert s11.Peek(33) == 0x11;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s12, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 118
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[4] == 0xa8a

    requires s0.stack[9] == 0x790

    requires s0.stack[17] == 0x560

    requires s0.stack[21] == 0x450

    requires s0.stack[25] == 0x367

    requires s0.stack[29] == 0x91

    requires s0.stack[32] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa8a;
      assert s1.Peek(9) == 0x790;
      assert s1.Peek(17) == 0x560;
      assert s1.Peek(21) == 0x450;
      assert s1.Peek(25) == 0x367;
      assert s1.Peek(29) == 0x91;
      assert s1.Peek(32) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s8, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 120
    * Starting at 0xa8a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa8a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[4] == 0x790

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x790;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x367;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s10, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 74
    * Starting at 0x790
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x790 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[8] == 0x560

    requires s0.stack[12] == 0x450

    requires s0.stack[16] == 0x367

    requires s0.stack[20] == 0x91

    requires s0.stack[23] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x560;
      assert s1.Peek(12) == 0x450;
      assert s1.Peek(16) == 0x367;
      assert s1.Peek(20) == 0x91;
      assert s1.Peek(23) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Gas(s9);
      var s11 := DelegateCall(s10);
      assert s11.Peek(9) == 0x560;
      assert s11.Peek(13) == 0x450;
      assert s11.Peek(17) == 0x367;
      assert s11.Peek(21) == 0x91;
      assert s11.Peek(24) == 0x11;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x07cb);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s21, gas - 1)
      else
        ExecuteFromCFGNode_s126(s21, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 75
    * Starting at 0x7aa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[9] == 0x560

    requires s0.stack[13] == 0x450

    requires s0.stack[17] == 0x367

    requires s0.stack[21] == 0x91

    requires s0.stack[24] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x560;
      assert s1.Peek(14) == 0x450;
      assert s1.Peek(18) == 0x367;
      assert s1.Peek(22) == 0x91;
      assert s1.Peek(25) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := Push1(s6, 0x3f);
      var s8 := ReturnDataSize(s7);
      var s9 := Add(s8);
      var s10 := And(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x560;
      assert s11.Peek(15) == 0x450;
      assert s11.Peek(19) == 0x367;
      assert s11.Peek(23) == 0x91;
      assert s11.Peek(26) == 0x11;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup3(s15);
      var s17 := MStore(s16);
      var s18 := ReturnDataSize(s17);
      var s19 := Push1(s18, 0x00);
      var s20 := Push1(s19, 0x20);
      var s21 := Dup5(s20);
      assert s21.Peek(13) == 0x560;
      assert s21.Peek(17) == 0x450;
      assert s21.Peek(21) == 0x367;
      assert s21.Peek(25) == 0x91;
      assert s21.Peek(28) == 0x11;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x07d0);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s25, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 77
    * Starting at 0x7d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[9] == 0x560

    requires s0.stack[13] == 0x450

    requires s0.stack[17] == 0x367

    requires s0.stack[21] == 0x91

    requires s0.stack[24] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x560;
      assert s1.Peek(13) == 0x450;
      assert s1.Peek(17) == 0x367;
      assert s1.Peek(21) == 0x91;
      assert s1.Peek(24) == 0x11;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x07e1);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x7e1;
      assert s11.Peek(11) == 0x560;
      assert s11.Peek(15) == 0x450;
      assert s11.Peek(19) == 0x367;
      assert s11.Peek(23) == 0x91;
      assert s11.Peek(26) == 0x11;
      var s12 := Push2(s11, 0x07eb);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s13, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 79
    * Starting at 0x7eb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[4] == 0x7e1

    requires s0.stack[11] == 0x560

    requires s0.stack[15] == 0x450

    requires s0.stack[19] == 0x367

    requires s0.stack[23] == 0x91

    requires s0.stack[26] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7e1;
      assert s1.Peek(11) == 0x560;
      assert s1.Peek(15) == 0x450;
      assert s1.Peek(19) == 0x367;
      assert s1.Peek(23) == 0x91;
      assert s1.Peek(26) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0881);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s6, gas - 1)
      else
        ExecuteFromCFGNode_s129(s6, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 80
    * Starting at 0x7f4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x367;
      assert s1.Peek(25) == 0x91;
      assert s1.Peek(28) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Sub(s3);
      var s5 := Push2(s4, 0x087a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s6, gas - 1)
      else
        ExecuteFromCFGNode_s130(s6, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 81
    * Starting at 0x7fd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push20(s0, 0xffffffffffffffffffffffffffffffffffffffff);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x367;
      assert s1.Peek(25) == 0x91;
      assert s1.Peek(28) == 0x11;
      var s2 := Dup6(s1);
      var s3 := And(s2);
      var s4 := ExtCodeSize(s3);
      var s5 := Push2(s4, 0x087a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s6, gas - 1)
      else
        ExecuteFromCFGNode_s131(s6, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 82
    * Starting at 0x819
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x819 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x367;
      assert s1.Peek(25) == 0x91;
      assert s1.Peek(28) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x1d);
      assert s11.Peek(7) == 0x7e1;
      assert s11.Peek(14) == 0x560;
      assert s11.Peek(18) == 0x450;
      assert s11.Peek(22) == 0x367;
      assert s11.Peek(26) == 0x91;
      assert s11.Peek(29) == 0x11;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(7) == 0x7e1;
      assert s21.Peek(14) == 0x560;
      assert s21.Peek(18) == 0x450;
      assert s21.Peek(22) == 0x367;
      assert s21.Peek(26) == 0x91;
      assert s21.Peek(29) == 0x11;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0286);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s24, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[6] == 0x7e1

    requires s0.stack[13] == 0x560

    requires s0.stack[17] == 0x450

    requires s0.stack[21] == 0x367

    requires s0.stack[25] == 0x91

    requires s0.stack[28] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x7e1;
      assert s1.Peek(13) == 0x560;
      assert s1.Peek(17) == 0x450;
      assert s1.Peek(21) == 0x367;
      assert s1.Peek(25) == 0x91;
      assert s1.Peek(28) == 0x11;
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

  /** Node 133
    * Segment Id for this node is: 83
    * Starting at 0x87a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7e1;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x367;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x088b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s5, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 85
    * Starting at 0x88b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7e1;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x367;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
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
    * Segment Id for this node is: 78
    * Starting at 0x7e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x560

    requires s0.stack[11] == 0x450

    requires s0.stack[15] == 0x367

    requires s0.stack[19] == 0x91

    requires s0.stack[22] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x560;
      assert s1.Peek(11) == 0x450;
      assert s1.Peek(15) == 0x367;
      assert s1.Peek(19) == 0x91;
      assert s1.Peek(22) == 0x11;
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
      ExecuteFromCFGNode_s136(s10, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 64
    * Starting at 0x560
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x560 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[4] == 0x450

    requires s0.stack[8] == 0x367

    requires s0.stack[12] == 0x91

    requires s0.stack[15] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x450;
      assert s1.Peek(8) == 0x367;
      assert s1.Peek(12) == 0x91;
      assert s1.Peek(15) == 0x11;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 51
    * Starting at 0x450
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x367

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x367;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Pop(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s138(s2, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 52
    * Starting at 0x452
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x367

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x367;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s5, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 32
    * Starting at 0x367
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x367 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x91

    requires s0.stack[6] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MStore(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x91;
      assert s11.Peek(10) == 0x11;
      var s12 := MStore(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Swap1(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s19, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 84
    * Starting at 0x881
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x881 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x7e1

    requires s0.stack[12] == 0x560

    requires s0.stack[16] == 0x450

    requires s0.stack[20] == 0x367

    requires s0.stack[24] == 0x91

    requires s0.stack[27] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x7e1;
      assert s1.Peek(12) == 0x560;
      assert s1.Peek(16) == 0x450;
      assert s1.Peek(20) == 0x367;
      assert s1.Peek(24) == 0x91;
      assert s1.Peek(27) == 0x11;
      var s2 := Push2(s1, 0x088b);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0893);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s6, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 86
    * Starting at 0x893
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x893 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0x88b

    requires s0.stack[8] == 0x7e1

    requires s0.stack[15] == 0x560

    requires s0.stack[19] == 0x450

    requires s0.stack[23] == 0x367

    requires s0.stack[27] == 0x91

    requires s0.stack[30] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x88b;
      assert s1.Peek(8) == 0x7e1;
      assert s1.Peek(15) == 0x560;
      assert s1.Peek(19) == 0x450;
      assert s1.Peek(23) == 0x367;
      assert s1.Peek(27) == 0x91;
      assert s1.Peek(30) == 0x11;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x08a3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s6, gas - 1)
      else
        ExecuteFromCFGNode_s142(s6, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 87
    * Starting at 0x89b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x89b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0x88b

    requires s0.stack[8] == 0x7e1

    requires s0.stack[15] == 0x560

    requires s0.stack[19] == 0x450

    requires s0.stack[23] == 0x367

    requires s0.stack[27] == 0x91

    requires s0.stack[30] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x88b;
      assert s1.Peek(9) == 0x7e1;
      assert s1.Peek(16) == 0x560;
      assert s1.Peek(20) == 0x450;
      assert s1.Peek(24) == 0x367;
      assert s1.Peek(28) == 0x91;
      assert s1.Peek(31) == 0x11;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 143
    * Segment Id for this node is: 88
    * Starting at 0x8a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[2] == 0x88b

    requires s0.stack[8] == 0x7e1

    requires s0.stack[15] == 0x560

    requires s0.stack[19] == 0x450

    requires s0.stack[23] == 0x367

    requires s0.stack[27] == 0x91

    requires s0.stack[30] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x88b;
      assert s1.Peek(8) == 0x7e1;
      assert s1.Peek(15) == 0x560;
      assert s1.Peek(19) == 0x450;
      assert s1.Peek(23) == 0x367;
      assert s1.Peek(27) == 0x91;
      assert s1.Peek(30) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push32(s4, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0286);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x286;
      assert s11.Peek(5) == 0x88b;
      assert s11.Peek(11) == 0x7e1;
      assert s11.Peek(18) == 0x560;
      assert s11.Peek(22) == 0x450;
      assert s11.Peek(26) == 0x367;
      assert s11.Peek(30) == 0x91;
      assert s11.Peek(33) == 0x11;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0a94);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s14, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 121
    * Starting at 0xa94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[2] == 0x286

    requires s0.stack[5] == 0x88b

    requires s0.stack[11] == 0x7e1

    requires s0.stack[18] == 0x560

    requires s0.stack[22] == 0x450

    requires s0.stack[26] == 0x367

    requires s0.stack[30] == 0x91

    requires s0.stack[33] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x286;
      assert s1.Peek(5) == 0x88b;
      assert s1.Peek(11) == 0x7e1;
      assert s1.Peek(18) == 0x560;
      assert s1.Peek(22) == 0x450;
      assert s1.Peek(26) == 0x367;
      assert s1.Peek(30) == 0x91;
      assert s1.Peek(33) == 0x11;
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
      assert s11.Peek(6) == 0x286;
      assert s11.Peek(9) == 0x88b;
      assert s11.Peek(15) == 0x7e1;
      assert s11.Peek(22) == 0x560;
      assert s11.Peek(26) == 0x450;
      assert s11.Peek(30) == 0x367;
      assert s11.Peek(34) == 0x91;
      assert s11.Peek(37) == 0x11;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0ab3);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0a54);
      assert s21.Peek(0) == 0xa54;
      assert s21.Peek(4) == 0xab3;
      assert s21.Peek(9) == 0x286;
      assert s21.Peek(12) == 0x88b;
      assert s21.Peek(18) == 0x7e1;
      assert s21.Peek(25) == 0x560;
      assert s21.Peek(29) == 0x450;
      assert s21.Peek(33) == 0x367;
      assert s21.Peek(37) == 0x91;
      assert s21.Peek(40) == 0x11;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s22, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 115
    * Starting at 0xa54
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 40

    requires s0.stack[3] == 0xab3

    requires s0.stack[8] == 0x286

    requires s0.stack[11] == 0x88b

    requires s0.stack[17] == 0x7e1

    requires s0.stack[24] == 0x560

    requires s0.stack[28] == 0x450

    requires s0.stack[32] == 0x367

    requires s0.stack[36] == 0x91

    requires s0.stack[39] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xab3;
      assert s1.Peek(8) == 0x286;
      assert s1.Peek(11) == 0x88b;
      assert s1.Peek(17) == 0x7e1;
      assert s1.Peek(24) == 0x560;
      assert s1.Peek(28) == 0x450;
      assert s1.Peek(32) == 0x367;
      assert s1.Peek(36) == 0x91;
      assert s1.Peek(39) == 0x11;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s146(s2, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 116
    * Starting at 0xa57
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa57 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[4] == 0xab3

    requires s0.stack[9] == 0x286

    requires s0.stack[12] == 0x88b

    requires s0.stack[18] == 0x7e1

    requires s0.stack[25] == 0x560

    requires s0.stack[29] == 0x450

    requires s0.stack[33] == 0x367

    requires s0.stack[37] == 0x91

    requires s0.stack[40] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xab3;
      assert s1.Peek(9) == 0x286;
      assert s1.Peek(12) == 0x88b;
      assert s1.Peek(18) == 0x7e1;
      assert s1.Peek(25) == 0x560;
      assert s1.Peek(29) == 0x450;
      assert s1.Peek(33) == 0x367;
      assert s1.Peek(37) == 0x91;
      assert s1.Peek(40) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0a6f);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s7, gas - 1)
      else
        ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 117
    * Starting at 0xa60
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa60 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[4] == 0xab3

    requires s0.stack[9] == 0x286

    requires s0.stack[12] == 0x88b

    requires s0.stack[18] == 0x7e1

    requires s0.stack[25] == 0x560

    requires s0.stack[29] == 0x450

    requires s0.stack[33] == 0x367

    requires s0.stack[37] == 0x91

    requires s0.stack[40] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0xab3;
      assert s1.Peek(10) == 0x286;
      assert s1.Peek(13) == 0x88b;
      assert s1.Peek(19) == 0x7e1;
      assert s1.Peek(26) == 0x560;
      assert s1.Peek(30) == 0x450;
      assert s1.Peek(34) == 0x367;
      assert s1.Peek(38) == 0x91;
      assert s1.Peek(41) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0a57);
      assert s11.Peek(0) == 0xa57;
      assert s11.Peek(5) == 0xab3;
      assert s11.Peek(10) == 0x286;
      assert s11.Peek(13) == 0x88b;
      assert s11.Peek(19) == 0x7e1;
      assert s11.Peek(26) == 0x560;
      assert s11.Peek(30) == 0x450;
      assert s11.Peek(34) == 0x367;
      assert s11.Peek(38) == 0x91;
      assert s11.Peek(41) == 0x11;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s12, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 118
    * Starting at 0xa6f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 41

    requires s0.stack[4] == 0xab3

    requires s0.stack[9] == 0x286

    requires s0.stack[12] == 0x88b

    requires s0.stack[18] == 0x7e1

    requires s0.stack[25] == 0x560

    requires s0.stack[29] == 0x450

    requires s0.stack[33] == 0x367

    requires s0.stack[37] == 0x91

    requires s0.stack[40] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xab3;
      assert s1.Peek(9) == 0x286;
      assert s1.Peek(12) == 0x88b;
      assert s1.Peek(18) == 0x7e1;
      assert s1.Peek(25) == 0x560;
      assert s1.Peek(29) == 0x450;
      assert s1.Peek(33) == 0x367;
      assert s1.Peek(37) == 0x91;
      assert s1.Peek(40) == 0x11;
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
    * Segment Id for this node is: 122
    * Starting at 0xab3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xab3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 36

    requires s0.stack[4] == 0x286

    requires s0.stack[7] == 0x88b

    requires s0.stack[13] == 0x7e1

    requires s0.stack[20] == 0x560

    requires s0.stack[24] == 0x450

    requires s0.stack[28] == 0x367

    requires s0.stack[32] == 0x91

    requires s0.stack[35] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x286;
      assert s1.Peek(7) == 0x88b;
      assert s1.Peek(13) == 0x7e1;
      assert s1.Peek(20) == 0x560;
      assert s1.Peek(24) == 0x450;
      assert s1.Peek(28) == 0x367;
      assert s1.Peek(32) == 0x91;
      assert s1.Peek(35) == 0x11;
      var s2 := Push1(s1, 0x1f);
      var s3 := Add(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := And(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x286;
      assert s11.Peek(6) == 0x88b;
      assert s11.Peek(12) == 0x7e1;
      assert s11.Peek(19) == 0x560;
      assert s11.Peek(23) == 0x450;
      assert s11.Peek(27) == 0x367;
      assert s11.Peek(31) == 0x91;
      assert s11.Peek(34) == 0x11;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s16, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0x88b

    requires s0.stack[9] == 0x7e1

    requires s0.stack[16] == 0x560

    requires s0.stack[20] == 0x450

    requires s0.stack[24] == 0x367

    requires s0.stack[28] == 0x91

    requires s0.stack[31] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x88b;
      assert s1.Peek(9) == 0x7e1;
      assert s1.Peek(16) == 0x560;
      assert s1.Peek(20) == 0x450;
      assert s1.Peek(24) == 0x367;
      assert s1.Peek(28) == 0x91;
      assert s1.Peek(31) == 0x11;
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
    * Segment Id for this node is: 76
    * Starting at 0x7cb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[9] == 0x560

    requires s0.stack[13] == 0x450

    requires s0.stack[17] == 0x367

    requires s0.stack[21] == 0x91

    requires s0.stack[24] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x560;
      assert s1.Peek(13) == 0x450;
      assert s1.Peek(17) == 0x367;
      assert s1.Peek(21) == 0x91;
      assert s1.Peek(24) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s127(s4, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 11
    * Starting at 0xe9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11;
      var s2 := Push32(s1, 0x70d7c69000000000000000000000000000000000000000000000000000000000);
      var s3 := Push32(s2, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x013a);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s8, gas - 1)
      else
        ExecuteFromCFGNode_s153(s8, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 12
    * Starting at 0x133
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0091);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push2(s1, 0x037e);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s3, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 33
    * Starting at 0x37e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x91

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0388);
      var s4 := Push2(s3, 0x0420);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s155(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 44
    * Starting at 0x420
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x388

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x388;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x029f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s5, gas - 1)
      else
        ExecuteFromCFGNode_s156(s5, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 45
    * Starting at 0x427
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x427 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x388

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(1) == 0x388;
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 157
    * Segment Id for this node is: 21
    * Starting at 0x29f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x388

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x388;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s158(s2, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 34
    * Starting at 0x388
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x388 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x91

    requires s0.stack[4] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x91;
      assert s1.Peek(4) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0397);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push2(s7, 0x08d7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s9, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 89
    * Starting at 0x8d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x397

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x397;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Dup6(s3);
      var s5 := Dup6(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x08e7);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s9, gas - 1)
      else
        ExecuteFromCFGNode_s160(s9, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 90
    * Starting at 0x8e3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x397

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x397;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 161
    * Segment Id for this node is: 91
    * Starting at 0x8e7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x397

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x397;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Dup4(s1);
      var s3 := Dup7(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x08f4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s7, gas - 1)
      else
        ExecuteFromCFGNode_s162(s7, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 92
    * Starting at 0x8f0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x397

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x397;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 163
    * Segment Id for this node is: 93
    * Starting at 0x8f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x397

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x397;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap4(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := Sub(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(1) == 0x397;
      assert s11.Peek(6) == 0x91;
      assert s11.Peek(9) == 0x11;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s13, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 35
    * Starting at 0x397
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x397 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x91

    requires s0.stack[7] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x91;
      assert s1.Peek(7) == 0x11;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push2(s4, 0x03a4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x092a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s9, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 97
    * Starting at 0x92a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x3a4

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3a4;
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x093c);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s10, gas - 1)
      else
        ExecuteFromCFGNode_s166(s10, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 98
    * Starting at 0x938
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a4

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 167
    * Segment Id for this node is: 99
    * Starting at 0x93c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x3a4

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3a4;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push2(s1, 0x0560);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x0901);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s5, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 94
    * Starting at 0x901
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x901 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x560

    requires s0.stack[5] == 0x3a4

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x560;
      assert s1.Peek(5) == 0x3a4;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0925);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s10, gas - 1)
      else
        ExecuteFromCFGNode_s169(s10, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 95
    * Starting at 0x921
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x921 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x560

    requires s0.stack[6] == 0x3a4

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x560;
      assert s1.Peek(7) == 0x3a4;
      assert s1.Peek(10) == 0x91;
      assert s1.Peek(13) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 170
    * Segment Id for this node is: 96
    * Starting at 0x925
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x925 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x560

    requires s0.stack[6] == 0x3a4

    requires s0.stack[9] == 0x91

    requires s0.stack[12] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x560;
      assert s1.Peek(6) == 0x3a4;
      assert s1.Peek(9) == 0x91;
      assert s1.Peek(12) == 0x11;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s5, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 64
    * Starting at 0x560
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x560 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x3a4

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s7, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 36
    * Starting at 0x3a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x91

    requires s0.stack[6] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0324);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0457);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s173(s7, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 53
    * Starting at 0x457
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x91

    requires s0.stack[7] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x91;
      assert s1.Peek(7) == 0x11;
      var s2 := Push32(s1, 0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f);
      var s3 := Push2(s2, 0x0480);
      var s4 := Push2(s3, 0x02a1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s5, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 22
    * Starting at 0x2a1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x480

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x480;
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s175(s3, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 23
    * Starting at 0x2c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x480

    requires s0.stack[5] == 0x324

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x480;
      assert s1.Peek(5) == 0x324;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := SLoad(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s8, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 54
    * Starting at 0x480
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x480 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(5) == 0x324;
      assert s11.Peek(8) == 0x91;
      assert s11.Peek(11) == 0x11;
      var s12 := Dup5(s11);
      var s13 := And(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup4(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Add(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := MLoad(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(5) == 0x324;
      assert s21.Peek(8) == 0x91;
      assert s21.Peek(11) == 0x11;
      var s22 := Swap2(s21);
      var s23 := Sub(s22);
      var s24 := Swap1(s23);
      var s25 := Log1(s24);
      var s26 := Push2(s25, 0x04b8);
      var s27 := Dup2(s26);
      var s28 := Push2(s27, 0x0567);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s29, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 65
    * Starting at 0x567
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x567 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x4b8

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b8;
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Push2(s4, 0x060a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s180(s6, gas - 1)
      else
        ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 66
    * Starting at 0x583
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x583 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x4b8

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x4b8;
      assert s1.Peek(4) == 0x324;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
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
      assert s11.Peek(3) == 0x4b8;
      assert s11.Peek(5) == 0x324;
      assert s11.Peek(8) == 0x91;
      assert s11.Peek(11) == 0x11;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x455243313936373a206e65772061646d696e20697320746865207a65726f2061);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x6464726573730000000000000000000000000000000000000000000000000000);
      assert s21.Peek(3) == 0x4b8;
      assert s21.Peek(5) == 0x324;
      assert s21.Peek(8) == 0x91;
      assert s21.Peek(11) == 0x11;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x0286);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s29, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x4b8

    requires s0.stack[4] == 0x324

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4b8;
      assert s1.Peek(4) == 0x324;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
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

  /** Node 180
    * Segment Id for this node is: 67
    * Starting at 0x60a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x4b8

    requires s0.stack[3] == 0x324

    requires s0.stack[6] == 0x91

    requires s0.stack[9] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b8;
      assert s1.Peek(3) == 0x324;
      assert s1.Peek(6) == 0x91;
      assert s1.Peek(9) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s181(s3, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 68
    * Starting at 0x62d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x4b8

    requires s0.stack[5] == 0x324

    requires s0.stack[8] == 0x91

    requires s0.stack[11] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4b8;
      assert s1.Peek(5) == 0x324;
      assert s1.Peek(8) == 0x91;
      assert s1.Peek(11) == 0x11;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffff0000000000000000000000000000000000000000);
      var s5 := And(s4);
      var s6 := Push20(s5, 0xffffffffffffffffffffffffffffffffffffffff);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Swap3(s8);
      var s10 := And(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(4) == 0x4b8;
      assert s11.Peek(6) == 0x324;
      assert s11.Peek(9) == 0x91;
      assert s11.Peek(12) == 0x11;
      var s12 := Swap1(s11);
      var s13 := Swap2(s12);
      var s14 := Or(s13);
      var s15 := Swap1(s14);
      var s16 := SStore(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s18, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 55
    * Starting at 0x4b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x324

    requires s0.stack[4] == 0x91

    requires s0.stack[7] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x324;
      assert s1.Peek(4) == 0x91;
      assert s1.Peek(7) == 0x11;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s3, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 13
    * Starting at 0x13a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11;
      var s2 := Push32(s1, 0x07ae5bc000000000000000000000000000000000000000000000000000000000);
      var s3 := Push32(s2, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x018b);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s8, gas - 1)
      else
        ExecuteFromCFGNode_s184(s8, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 14
    * Starting at 0x184
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x184 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0091);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push2(s1, 0x03af);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s185(s3, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 37
    * Starting at 0x3af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x91

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x03b9);
      var s4 := Push2(s3, 0x0420);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s5, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 44
    * Starting at 0x420
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3b9

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3b9;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x029f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s5, gas - 1)
      else
        ExecuteFromCFGNode_s187(s5, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 45
    * Starting at 0x427
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x427 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3b9

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(1) == 0x3b9;
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 188
    * Segment Id for this node is: 21
    * Starting at 0x29f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x3b9

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3b9;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s2, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 38
    * Starting at 0x3b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x91

    requires s0.stack[4] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x91;
      assert s1.Peek(4) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x03c3);
      var s4 := Push2(s3, 0x02a1);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 22
    * Starting at 0x2a1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x3c3

    requires s0.stack[3] == 0x91

    requires s0.stack[6] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c3;
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s191(s3, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 23
    * Starting at 0x2c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x3c3

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c3;
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := SLoad(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s8, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 39
    * Starting at 0x3c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x91

    requires s0.stack[6] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := Dup4(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x91;
      assert s11.Peek(8) == 0x11;
      var s12 := Swap2(s11);
      var s13 := Swap3(s12);
      var s14 := Pop(s13);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := MLoad(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup2(s18);
      var s20 := Dup4(s19);
      var s21 := Sub(s20);
      assert s21.Peek(6) == 0x91;
      assert s21.Peek(9) == 0x11;
      var s22 := Sub(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Push1(s25, 0x40);
      var s27 := MStore(s26);
      var s28 := Swap2(s27);
      var s29 := Pop(s28);
      var s30 := Pop(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(0) == 0x91;
      assert s31.Peek(4) == 0x11;
      var s32 := Jump(s31);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s32, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 15
    * Starting at 0x18b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11;
      var s2 := Push32(s1, 0xa39f25e500000000000000000000000000000000000000000000000000000000);
      var s3 := Push32(s2, 0xffffffff00000000000000000000000000000000000000000000000000000000);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x01dc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s8, gas - 1)
      else
        ExecuteFromCFGNode_s194(s8, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 16
    * Starting at 0x1d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0091);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push2(s1, 0x03fc);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s3, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 40
    * Starting at 0x3fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x91

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x91;
      assert s1.Peek(3) == 0x11;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0406);
      var s4 := Push2(s3, 0x0420);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s5, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 44
    * Starting at 0x420
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x420 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x406

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x406;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := CallValue(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x029f);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s198(s5, gas - 1)
      else
        ExecuteFromCFGNode_s197(s5, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 45
    * Starting at 0x427
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x427 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x406

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(1) == 0x406;
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 198
    * Segment Id for this node is: 21
    * Starting at 0x29f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x406

    requires s0.stack[2] == 0x91

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x406;
      assert s1.Peek(2) == 0x91;
      assert s1.Peek(5) == 0x11;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s2, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 41
    * Starting at 0x406
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x406 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x91

    requires s0.stack[4] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x91;
      assert s1.Peek(4) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x03c3);
      var s4 := Push2(s3, 0x04bb);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s5, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 56
    * Starting at 0x4bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x3c3

    requires s0.stack[3] == 0x91

    requires s0.stack[6] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3c3;
      assert s1.Peek(3) == 0x91;
      assert s1.Peek(6) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x04c5);
      var s4 := Push2(s3, 0x0673);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s5, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 69
    * Starting at 0x673
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x673 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[0] == 0x4c5

    requires s0.stack[2] == 0x3c3

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4c5;
      assert s1.Peek(2) == 0x3c3;
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x02c5);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s5, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 23
    * Starting at 0x2c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x4c5

    requires s0.stack[4] == 0x3c3

    requires s0.stack[7] == 0x91

    requires s0.stack[10] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4c5;
      assert s1.Peek(4) == 0x3c3;
      assert s1.Peek(7) == 0x91;
      assert s1.Peek(10) == 0x11;
      var s2 := SLoad(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s8, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 57
    * Starting at 0x4c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x3c3

    requires s0.stack[5] == 0x91

    requires s0.stack[8] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c3;
      assert s1.Peek(5) == 0x91;
      assert s1.Peek(8) == 0x11;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s5, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 17
    * Starting at 0x1dc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[2] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(3) == 0x11;
      var s12 := Push1(s11, 0x42);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(3) == 0x11;
      var s22 := Push32(s21, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s23 := Push1(s22, 0x64);
      var s24 := Dup3(s23);
      var s25 := Add(s24);
      var s26 := MStore(s25);
      var s27 := Push32(s26, 0x6574000000000000000000000000000000000000000000000000000000000000);
      var s28 := Push1(s27, 0x84);
      var s29 := Dup3(s28);
      var s30 := Add(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x11;
      var s32 := Push1(s31, 0xa4);
      var s33 := Add(s32);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s205(s33, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 18
    * Starting at 0x286
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x286 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11;
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

  /** Node 206
    * Segment Id for this node is: 20
    * Starting at 0x297
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x297 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x11;
      var s2 := Push2(s1, 0x029f);
      var s3 := Push2(s2, 0x0410);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s4, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 42
    * Starting at 0x410
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x410 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x29f

    requires s0.stack[1] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x29f;
      assert s1.Peek(1) == 0x11;
      var s2 := Push2(s1, 0x029f);
      var s3 := Push2(s2, 0x041b);
      var s4 := Push2(s3, 0x04bb);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s5, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 56
    * Starting at 0x4bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x41b

    requires s0.stack[1] == 0x29f

    requires s0.stack[2] == 0x29f

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x41b;
      assert s1.Peek(1) == 0x29f;
      assert s1.Peek(2) == 0x29f;
      assert s1.Peek(3) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x04c5);
      var s4 := Push2(s3, 0x0673);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s209(s5, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 69
    * Starting at 0x673
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x673 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x4c5

    requires s0.stack[2] == 0x41b

    requires s0.stack[3] == 0x29f

    requires s0.stack[4] == 0x29f

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4c5;
      assert s1.Peek(2) == 0x41b;
      assert s1.Peek(3) == 0x29f;
      assert s1.Peek(4) == 0x29f;
      assert s1.Peek(5) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x02c5);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s5, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 23
    * Starting at 0x2c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x4c5

    requires s0.stack[4] == 0x41b

    requires s0.stack[5] == 0x29f

    requires s0.stack[6] == 0x29f

    requires s0.stack[7] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4c5;
      assert s1.Peek(4) == 0x41b;
      assert s1.Peek(5) == 0x29f;
      assert s1.Peek(6) == 0x29f;
      assert s1.Peek(7) == 0x11;
      var s2 := SLoad(s1);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := And(s3);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s8, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 57
    * Starting at 0x4c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x41b

    requires s0.stack[3] == 0x29f

    requires s0.stack[4] == 0x29f

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x41b;
      assert s1.Peek(3) == 0x29f;
      assert s1.Peek(4) == 0x29f;
      assert s1.Peek(5) == 0x11;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s5, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 43
    * Starting at 0x41b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x29f

    requires s0.stack[2] == 0x29f

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x29f;
      assert s1.Peek(2) == 0x29f;
      assert s1.Peek(3) == 0x11;
      var s2 := Push2(s1, 0x04ca);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s213(s3, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 58
    * Starting at 0x4ca
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ca as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x29f

    requires s0.stack[2] == 0x29f

    requires s0.stack[3] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x29f;
      assert s1.Peek(2) == 0x29f;
      assert s1.Peek(3) == 0x11;
      var s2 := CallDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup1(s3);
      var s5 := CallDataCopy(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Dup1(s6);
      var s8 := CallDataSize(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup5(s9);
      var s11 := Gas(s10);
      assert s11.Peek(7) == 0x29f;
      assert s11.Peek(8) == 0x29f;
      assert s11.Peek(9) == 0x11;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x04e9);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s21, gas - 1)
      else
        ExecuteFromCFGNode_s214(s21, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 59
    * Starting at 0x4e5
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x29f

    requires s0.stack[4] == 0x29f

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x29f;
      assert s1.Peek(5) == 0x29f;
      assert s1.Peek(6) == 0x11;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 215
    * Segment Id for this node is: 60
    * Starting at 0x4e9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x29f

    requires s0.stack[4] == 0x29f

    requires s0.stack[5] == 0x11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x29f;
      assert s1.Peek(4) == 0x29f;
      assert s1.Peek(5) == 0x11;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 216
    * Segment Id for this node is: 3
    * Starting at 0x13
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0011);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }
}
