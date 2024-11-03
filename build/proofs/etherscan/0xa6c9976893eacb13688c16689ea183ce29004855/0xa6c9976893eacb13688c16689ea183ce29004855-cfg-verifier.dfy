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
      var s1 := Push1(s0, 0x40);
      var s2 := Push1(s1, 0x80);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := CallDataSize(s5);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0013);
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
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x13
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0xe0);
      var s4 := Dup2(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Dup2(s5);
      var s7 := Shr(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := Push4(s9, 0x3ddc29f5);
      var s11 := Eq(s10);
      var s12 := Push2(s11, 0x02cc);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s13, gas - 1)
      else
        ExecuteFromCFGNode_s3(s13, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x28
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Push4(s1, 0x757f1c84);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0037);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s5(s5, gas - 1)
      else
        ExecuteFromCFGNode_s4(s5, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 4
    * Starting at 0x33
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33 as nat
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

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x37
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallValue(s1);
      var s3 := Push2(s2, 0x02c9);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s4, gas - 1)
      else
        ExecuteFromCFGNode_s6(s4, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x3d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Push32(s1, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc);
      var s3 := CallDataSize(s2);
      var s4 := Add(s3);
      var s5 := SLt(s4);
      var s6 := Push2(s5, 0x02c9);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s7, gas - 1)
      else
        ExecuteFromCFGNode_s7(s7, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 7
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0xffffffffffffffff);
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x04);
      var s4 := CallDataLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x02c5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s86(s9, gas - 1)
      else
        ExecuteFromCFGNode_s8(s9, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 8
    * Starting at 0x7a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0087);
      assert s1.Peek(0) == 0x87;
      var s2 := Swap1(s1);
      var s3 := CallDataSize(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0672);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s8, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 90
    * Starting at 0x672
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x672 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x87

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x87;
      var s2 := Swap2(s1);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s10, gas - 1)
      else
        ExecuteFromCFGNode_s10(s10, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 91
    * Starting at 0x67f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x87

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(1) == 0x87;
      var s2 := CallDataLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup4(s4);
      var s6 := Gt(s5);
      var s7 := Push2(s6, 0x06a3);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s8, gas - 1)
      else
        ExecuteFromCFGNode_s11(s8, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 92
    * Starting at 0x691
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x691 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x87

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(2) == 0x87;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x05);
      var s8 := Shl(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(1) == 0x87;
      var s12 := Push2(s11, 0x06a3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s13, gas - 1)
      else
        ExecuteFromCFGNode_s12(s13, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 93
    * Starting at 0x6a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x87

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s1, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 9
    * Starting at 0x87
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Push1(s2, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Dup2(s5);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x02c1);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s9, gas - 1)
      else
        ExecuteFromCFGNode_s14(s9, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 10
    * Starting at 0x93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00a3);
      assert s1.Peek(0) == 0xa3;
      var s2 := Swap1(s1);
      var s3 := Swap5(s2);
      var s4 := Swap3(s3);
      var s5 := Swap5(s4);
      var s6 := CallDataSize(s5);
      var s7 := Swap1(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0672);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s11, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 90
    * Starting at 0x672
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x672 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xa3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xa3;
      var s2 := Swap2(s1);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s10, gas - 1)
      else
        ExecuteFromCFGNode_s16(s10, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 91
    * Starting at 0x67f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x67f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xa3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(1) == 0xa3;
      var s2 := CallDataLoad(s1);
      var s3 := Swap2(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup4(s4);
      var s6 := Gt(s5);
      var s7 := Push2(s6, 0x06a3);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s8, gas - 1)
      else
        ExecuteFromCFGNode_s17(s8, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 92
    * Starting at 0x691
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x691 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xa3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(2) == 0xa3;
      var s2 := Dup1(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Dup5(s5);
      var s7 := Push1(s6, 0x05);
      var s8 := Shl(s7);
      var s9 := Add(s8);
      var s10 := Add(s9);
      var s11 := Gt(s10);
      assert s11.Peek(1) == 0xa3;
      var s12 := Push2(s11, 0x06a3);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s13, gas - 1)
      else
        ExecuteFromCFGNode_s18(s13, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 93
    * Starting at 0x6a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xa3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s1, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 11
    * Starting at 0xa3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap3(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0x00ae);
      var s5 := Dup8(s4);
      var s6 := Push2(s5, 0x077a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s7, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 103
    * Starting at 0x77a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xae

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae;
      var s2 := Push8(s1, 0xffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x070a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s80(s6, gas - 1)
      else
        ExecuteFromCFGNode_s21(s6, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 104
    * Starting at 0x78a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xae

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(2) == 0xae;
      var s2 := Shl(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s6, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 12
    * Starting at 0xae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap4(s1);
      var s3 := Push2(s2, 0x00bb);
      var s4 := Dup7(s3);
      var s5 := MLoad(s4);
      var s6 := Swap6(s5);
      var s7 := Dup7(s6);
      var s8 := Push2(s7, 0x0739);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s9, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 101
    * Starting at 0x739
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0xbb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbb;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0xbb;
      var s12 := Lt(s11);
      var s13 := Push8(s12, 0xffffffffffffffff);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := Or(s15);
      var s17 := Push2(s16, 0x070a);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s18, gas - 1)
      else
        ExecuteFromCFGNode_s24(s18, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 102
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0xbb;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s25(s3, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 13
    * Starting at 0xbb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup8(s1);
      var s3 := Dup6(s2);
      var s4 := MStore(s3);
      var s5 := Push2(s4, 0x00c7);
      var s6 := Dup9(s5);
      var s7 := Push2(s6, 0x077a);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s8, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 103
    * Starting at 0x77a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xc7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc7;
      var s2 := Push8(s1, 0xffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x070a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s6, gas - 1)
      else
        ExecuteFromCFGNode_s27(s6, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 104
    * Starting at 0x78a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xc7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(2) == 0xc7;
      var s2 := Shl(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s6, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 14
    * Starting at 0xc7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap3(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Dup5(s5);
      var s7 := Dup9(s6);
      var s8 := Add(s7);
      var s9 := Swap4(s8);
      var s10 := Add(s9);
      var s11 := CallDataSize(s10);
      var s12 := Dup5(s11);
      var s13 := CallDataCopy(s12);
      var s14 := Push32(s13, 0x000000000000000000000000d85ee50da419cc5af83a1e70a91d5c630b8c650a);
      var s15 := Push20(s14, 0xffffffffffffffffffffffffffffffffffffffff);
      var s16 := And(s15);
      var s17 := Swap2(s16);
      var s18 := Dup6(s17);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s29(s18, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 15
    * Starting at 0x12e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0xffffffff);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Swap2(s6);
      var s8 := Dup14(s7);
      var s9 := Dup4(s8);
      var s10 := Lt(s9);
      var s11 := IsZero(s10);
      var s12 := Push2(s11, 0x027f);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s13, gas - 1)
      else
        ExecuteFromCFGNode_s30(s13, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 16
    * Starting at 0x141
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x141 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0155);
      assert s1.Peek(0) == 0x155;
      var s2 := Push2(s1, 0x0150);
      var s3 := Dup16(s2);
      var s4 := Dup16(s3);
      var s5 := Swap1(s4);
      var s6 := Dup7(s5);
      var s7 := Swap2(s6);
      var s8 := Push2(s7, 0x082b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s9, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 116
    * Starting at 0x82b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x150

    requires s0.stack[4] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x150;
      assert s1.Peek(4) == 0x155;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x07fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s8, gas - 1)
      else
        ExecuteFromCFGNode_s32(s8, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 117
    * Starting at 0x835
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x835 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x150

    requires s0.stack[3] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(3) == 0x150;
      assert s1.Peek(4) == 0x155;
      var s2 := Shl(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s5, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 17
    * Starting at 0x150
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x155;
      var s2 := Push2(s1, 0x083b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s3, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 118
    * Starting at 0x83b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x155;
      var s2 := CallDataLoad(s1);
      var s3 := Push4(s2, 0xffffffff);
      var s4 := Dup2(s3);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x06a3);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s9, gas - 1)
      else
        ExecuteFromCFGNode_s35(s9, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 119
    * Starting at 0x84a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0x155;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s2, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 18
    * Starting at 0x155
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x155 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0163);
      var s3 := Push2(s2, 0x0150);
      var s4 := Dup6(s3);
      var s5 := Dup8(s4);
      var s6 := Dup10(s5);
      var s7 := Push2(s6, 0x082b);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s8, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 116
    * Starting at 0x82b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[3] == 0x150

    requires s0.stack[4] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x150;
      assert s1.Peek(4) == 0x163;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x07fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s8, gas - 1)
      else
        ExecuteFromCFGNode_s38(s8, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 117
    * Starting at 0x835
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x835 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x150

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(3) == 0x150;
      assert s1.Peek(4) == 0x163;
      var s2 := Shl(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 17
    * Starting at 0x150
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push2(s1, 0x083b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s3, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 118
    * Starting at 0x83b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x83b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := CallDataLoad(s1);
      var s3 := Push4(s2, 0xffffffff);
      var s4 := Dup2(s3);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := Sub(s6);
      var s8 := Push2(s7, 0x06a3);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s9, gas - 1)
      else
        ExecuteFromCFGNode_s41(s9, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 119
    * Starting at 0x84a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x84a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(0) == 0x163;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s2, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 19
    * Starting at 0x163
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap2(s1);
      var s3 := Dup14(s2);
      var s4 := MLoad(s3);
      var s5 := Swap3(s4);
      var s6 := Dup2(s5);
      var s7 := Dup12(s6);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := Swap4(s9);
      var s11 := And(s10);
      var s12 := Dup4(s11);
      var s13 := MStore(s12);
      var s14 := And(s13);
      var s15 := Dup14(s14);
      var s16 := Dup4(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup13(s18);
      var s20 := Dup3(s19);
      var s21 := MStore(s20);
      var s22 := Push1(s21, 0x60);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := Swap1(s24);
      var s26 := Dup3(s25);
      var s27 := Dup3(s26);
      var s28 := Lt(s27);
      var s29 := Dup13(s28);
      var s30 := Dup4(s29);
      var s31 := Gt(s30);
      var s32 := Or(s31);
      var s33 := Push2(s32, 0x0252);
      var s34 := JumpI(s33);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s33.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s34, gas - 1)
      else
        ExecuteFromCFGNode_s43(s34, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 20
    * Starting at 0x188
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      var s2 := Dup15(s1);
      var s3 := MStore(s2);
      var s4 := Dup3(s3);
      var s5 := MLoad(s4);
      var s6 := Swap1(s5);
      var s7 := Keccak256(s6);
      var s8 := Push32(s7, 0xbc85694f00000000000000000000000000000000000000000000000000000000);
      var s9 := Dup3(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x64);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup9(s14);
      var s16 := Dup2(s15);
      var s17 := Push1(s16, 0x24);
      var s18 := Dup2(s17);
      var s19 := Dup11(s18);
      var s20 := Gas(s19);
      var s21 := StaticCall(s20);
      var s22 := Swap2(s21);
      var s23 := Dup3(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x0248);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s26, gas - 1)
      else
        ExecuteFromCFGNode_s44(s26, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 21
    * Starting at 0x1c6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 16
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup16(s0);
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Swap2(s3);
      var s5 := Dup11(s4);
      var s6 := Dup15(s5);
      var s7 := Swap3(s6);
      var s8 := Dup14(s7);
      var s9 := Swap5(s8);
      var s10 := Push2(s9, 0x01f7);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s11, gas - 1)
      else
        ExecuteFromCFGNode_s45(s11, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 22
    * Starting at 0x1d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x01e7);
      var s6 := Push2(s5, 0x01f0);
      var s7 := Swap5(s6);
      var s8 := Swap6(s7);
      var s9 := Push2(s8, 0xffff);
      var s10 := Swap3(s9);
      var s11 := Push2(s10, 0x07e8);
      assert s11.Peek(0) == 0x7e8;
      assert s11.Peek(3) == 0x1e7;
      assert s11.Peek(7) == 0x1f0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s12, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 113
    * Starting at 0x7e8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1e7

    requires s0.stack[6] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e7;
      assert s1.Peek(6) == 0x1f0;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x07fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s53(s8, gas - 1)
      else
        ExecuteFromCFGNode_s47(s8, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 114
    * Starting at 0x7f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1e7

    requires s0.stack[6] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(3) == 0x1e7;
      assert s1.Peek(7) == 0x1f0;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s8, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 23
    * Starting at 0x1e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1f0;
      var s2 := Swap2(s1);
      var s3 := And(s2);
      var s4 := Swap1(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0792);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s7, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 105
    * Starting at 0x792
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f0;
      var s2 := Push4(s1, 0xffffffff);
      var s3 := Dup1(s2);
      var s4 := Swap2(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x06be);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s10, gas - 1)
      else
        ExecuteFromCFGNode_s50(s10, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 106
    * Starting at 0x7a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(2) == 0x1f0;
      var s2 := Add(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s4, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 24
    * Starting at 0x1f0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x012e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s5, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 97
    * Starting at 0x6be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f0;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 53
    * Segment Id for this node is: 115
    * Starting at 0x7fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1e7

    requires s0.stack[6] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e7;
      assert s1.Peek(6) == 0x1f0;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 54
    * Segment Id for this node is: 25
    * Starting at 0x1f7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap5(s6);
      var s8 := Swap4(s7);
      var s9 := Pop(s8);
      var s10 := Dup2(s9);
      var s11 := ReturnDataSize(s10);
      var s12 := Dup4(s11);
      var s13 := Gt(s12);
      var s14 := Push2(s13, 0x0241);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s15, gas - 1)
      else
        ExecuteFromCFGNode_s55(s15, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 26
    * Starting at 0x208
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x208 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0212);
      var s3 := Dup2(s2);
      var s4 := Dup6(s3);
      var s5 := Push2(s4, 0x0739);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s6, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 101
    * Starting at 0x739
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[2] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x212;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x212;
      var s12 := Lt(s11);
      var s13 := Push8(s12, 0xffffffffffffffff);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := Or(s15);
      var s17 := Push2(s16, 0x070a);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s18, gas - 1)
      else
        ExecuteFromCFGNode_s57(s18, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 102
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x212;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s3, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 27
    * Starting at 0x212
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x212 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Sub(s3);
      var s5 := SLt(s4);
      var s6 := Push2(s5, 0x023d);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s65(s7, gas - 1)
      else
        ExecuteFromCFGNode_s59(s7, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 28
    * Starting at 0x21b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      var s2 := Dup11(s1);
      var s3 := Push2(s2, 0xffff);
      var s4 := Dup16(s3);
      var s5 := Swap5(s4);
      var s6 := Push2(s5, 0x01f0);
      var s7 := Swap5(s6);
      var s8 := Push2(s7, 0x0231);
      var s9 := Push2(s8, 0x01e7);
      var s10 := Swap3(s9);
      var s11 := Push2(s10, 0x07d9);
      assert s11.Peek(0) == 0x7d9;
      assert s11.Peek(2) == 0x231;
      assert s11.Peek(4) == 0x1e7;
      assert s11.Peek(8) == 0x1f0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s12, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 111
    * Starting at 0x7d9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x231

    requires s0.stack[3] == 0x1e7

    requires s0.stack[7] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x231;
      assert s1.Peek(3) == 0x1e7;
      assert s1.Peek(7) == 0x1f0;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0xffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s10, gas - 1)
      else
        ExecuteFromCFGNode_s61(s10, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 112
    * Starting at 0x7e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x231

    requires s0.stack[3] == 0x1e7

    requires s0.stack[7] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s1, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 29
    * Starting at 0x231
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x231 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1e7

    requires s0.stack[6] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e7;
      assert s1.Peek(6) == 0x1f0;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Dup13(s3);
      var s5 := Swap2(s4);
      var s6 := Swap(s5, 8);
      var s7 := Swap7(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x01d3);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s10, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 22
    * Starting at 0x1d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x1e7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x01e7);
      var s6 := Push2(s5, 0x01f0);
      var s7 := Swap5(s6);
      var s8 := Swap6(s7);
      var s9 := Push2(s8, 0xffff);
      var s10 := Swap3(s9);
      var s11 := Push2(s10, 0x07e8);
      assert s11.Peek(0) == 0x7e8;
      assert s11.Peek(3) == 0x1e7;
      assert s11.Peek(7) == 0x1f0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s12, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x231

    requires s0.stack[3] == 0x1e7

    requires s0.stack[7] == 0x1f0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x231;
      assert s1.Peek(3) == 0x1e7;
      assert s1.Peek(7) == 0x1f0;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 65
    * Segment Id for this node is: 30
    * Starting at 0x23d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 66
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x212

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x212;
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

  /** Node 67
    * Segment Id for this node is: 31
    * Starting at 0x241
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x241 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := ReturnDataSize(s2);
      var s4 := Push2(s3, 0x0208);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s5, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 32
    * Starting at 0x248
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x248 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup14(s1);
      var s3 := MLoad(s2);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup13(s4);
      var s6 := Dup3(s5);
      var s7 := ReturnDataCopy(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Swap1(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 69
    * Segment Id for this node is: 33
    * Starting at 0x252
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x252 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x24);
      var s3 := Dup12(s2);
      var s4 := Push32(s3, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x41);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 70
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 71
    * Segment Id for this node is: 115
    * Starting at 0x7fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x150

    requires s0.stack[3] == 0x163

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x150;
      assert s1.Peek(3) == 0x163;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 72
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x155;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 73
    * Segment Id for this node is: 115
    * Starting at 0x7fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x150

    requires s0.stack[3] == 0x155

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x150;
      assert s1.Peek(3) == 0x155;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 74
    * Segment Id for this node is: 34
    * Starting at 0x27f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 12
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup12(s1);
      var s3 := MLoad(s2);
      var s4 := Dup9(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Dup12(s6);
      var s8 := MLoad(s7);
      var s9 := Dup2(s8);
      var s10 := Dup11(s9);
      var s11 := Add(s10);
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Dup2(s14);
      var s16 := Swap1(s15);
      var s17 := Dup2(s16);
      var s18 := Dup16(s17);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Dup11(s20);
      var s22 := Swap1(s21);
      var s23 := Dup13(s22);
      var s24 := Dup15(s23);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s75(s24, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 35
    * Starting at 0x297
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x297 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x02a6);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s6, gas - 1)
      else
        ExecuteFromCFGNode_s76(s6, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 36
    * Starting at 0x29f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Sub(s4);
      var s6 := Swap1(s5);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 77
    * Segment Id for this node is: 37
    * Starting at 0x2a6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0xffff);
      var s5 := And(s4);
      var s6 := Dup6(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Swap6(s8);
      var s10 := Pop(s9);
      var s11 := Swap4(s10);
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Swap3(s17);
      var s19 := Push1(s18, 0x01);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0297);
      assert s21.Peek(0) == 0x297;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s22, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xc7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xc7;
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

  /** Node 79
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0xbb

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbb;
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

  /** Node 80
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xae

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xae;
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

  /** Node 81
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0xa3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 82
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0xa3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa3;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 83
    * Segment Id for this node is: 38
    * Starting at 0x2c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup5(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 84
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x87

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x87;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 85
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x87

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x87;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 86
    * Segment Id for this node is: 39
    * Starting at 0x2c5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 87
    * Segment Id for this node is: 40
    * Starting at 0x2c9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 88
    * Segment Id for this node is: 41
    * Starting at 0x2cc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := CallValue(s3);
      var s5 := Push2(s4, 0x066e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s6, gas - 1)
      else
        ExecuteFromCFGNode_s89(s6, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 42
    * Starting at 0x2d4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      var s2 := Push32(s1, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc);
      var s3 := CallDataSize(s2);
      var s4 := Add(s3);
      var s5 := SLt(s4);
      var s6 := Push2(s5, 0x066e);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s7, gas - 1)
      else
        ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 43
    * Starting at 0x2fd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0xffffffff);
      var s2 := Push1(s1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x066a);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s10, gas - 1)
      else
        ExecuteFromCFGNode_s91(s10, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 44
    * Starting at 0x30e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x24);
      var s2 := Swap5(s1);
      var s3 := Dup6(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := And(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := Dup2(s9);
      var s11 := Sub(s10);
      var s12 := Push2(s11, 0x0666);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s13, gas - 1)
      else
        ExecuteFromCFGNode_s92(s13, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 45
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x032b);
      assert s1.Peek(0) == 0x32b;
      var s2 := Dup5(s1);
      var s3 := Dup7(s2);
      var s4 := Swap3(s3);
      var s5 := Swap(s4, 9);
      var s6 := Swap6(s5);
      var s7 := Swap(s6, 9);
      var s8 := Push2(s7, 0x06a8);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s9, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 95
    * Starting at 0x6a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x32b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x32b;
      var s2 := Push4(s1, 0xffffffff);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Sub(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x32b;
      var s12 := Dup3(s11);
      var s13 := Gt(s12);
      var s14 := Push2(s13, 0x06be);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s15, gas - 1)
      else
        ExecuteFromCFGNode_s94(s15, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 96
    * Starting at 0x6bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x32b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s1, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 46
    * Starting at 0x32b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := And(s1);
      var s3 := Swap5(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := Push2(s4, 0x036f);
      var s6 := Push2(s5, 0x035a);
      var s7 := Dup9(s6);
      var s8 := Push2(s7, 0x077a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s9, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 103
    * Starting at 0x77a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x35a

    requires s0.stack[2] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x35a;
      assert s1.Peek(2) == 0x36f;
      var s2 := Push8(s1, 0xffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x070a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s6, gas - 1)
      else
        ExecuteFromCFGNode_s97(s6, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 104
    * Starting at 0x78a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x35a

    requires s0.stack[2] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(2) == 0x35a;
      assert s1.Peek(3) == 0x36f;
      var s2 := Shl(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s6, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 47
    * Starting at 0x35a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x36f;
      var s2 := Swap(s1, 8);
      var s3 := Push2(s2, 0x0367);
      var s4 := Dup7(s3);
      var s5 := MLoad(s4);
      var s6 := Swap(s5, 10);
      var s7 := Dup11(s6);
      var s8 := Push2(s7, 0x0739);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s9, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 101
    * Starting at 0x739
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x367

    requires s0.stack[4] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x367;
      assert s1.Peek(4) == 0x36f;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x367;
      assert s11.Peek(5) == 0x36f;
      var s12 := Lt(s11);
      var s13 := Push8(s12, 0xffffffffffffffff);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := Or(s15);
      var s17 := Push2(s16, 0x070a);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s190(s18, gas - 1)
      else
        ExecuteFromCFGNode_s100(s18, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 102
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x367

    requires s0.stack[3] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x367;
      assert s1.Peek(4) == 0x36f;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s3, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 48
    * Starting at 0x367
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x367 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x36f;
      var s2 := Dup1(s1);
      var s3 := Dup10(s2);
      var s4 := MStore(s3);
      var s5 := Push2(s4, 0x077a);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s6, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 103
    * Starting at 0x77a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x36f;
      var s2 := Push8(s1, 0xffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x070a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s6, gas - 1)
      else
        ExecuteFromCFGNode_s103(s6, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 104
    * Starting at 0x78a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x05);
      assert s1.Peek(2) == 0x36f;
      var s2 := Shl(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 49
    * Starting at 0x36f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Add(s1);
      var s3 := Dup5(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s105(s3, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 50
    * Starting at 0x372
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x372 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0607);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s6, gas - 1)
      else
        ExecuteFromCFGNode_s106(s6, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 51
    * Starting at 0x37a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      var s2 := Pop(s1);
      var s3 := Dup7(s2);
      var s4 := Swap4(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := Swap(s5, 8);
      var s7 := Dup9(s6);
      var s8 := Push32(s7, 0x000000000000000000000000d85ee50da419cc5af83a1e70a91d5c630b8c650a);
      var s9 := And(s8);
      var s10 := Swap6(s9);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s107(s10, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 52
    * Starting at 0x3b8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup8(s1);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup6(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0548);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s10, gas - 1)
      else
        ExecuteFromCFGNode_s108(s10, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 53
    * Starting at 0x3c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03cd);
      assert s1.Peek(0) == 0x3cd;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x06a8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s5, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 95
    * Starting at 0x6a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x3cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3cd;
      var s2 := Push4(s1, 0xffffffff);
      var s3 := Swap2(s2);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Sub(s8);
      var s10 := Swap2(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(1) == 0x3cd;
      var s12 := Dup3(s11);
      var s13 := Gt(s12);
      var s14 := Push2(s13, 0x06be);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s175(s15, gas - 1)
      else
        ExecuteFromCFGNode_s110(s15, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 96
    * Starting at 0x6bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x3cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s1, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 54
    * Starting at 0x3cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup8(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Push32(s4, 0xa17b920b00000000000000000000000000000000000000000000000000000000);
      var s6 := Dup4(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      var s12 := Dup2(s11);
      var s13 := Dup14(s12);
      var s14 := Push2(s13, 0x0160);
      var s15 := Swap4(s14);
      var s16 := Dup5(s15);
      var s17 := Swap2(s16);
      var s18 := Dup2(s17);
      var s19 := Dup14(s18);
      var s20 := Gas(s19);
      var s21 := StaticCall(s20);
      var s22 := Swap3(s21);
      var s23 := Dup4(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x053e);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s26, gas - 1)
      else
        ExecuteFromCFGNode_s112(s26, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 55
    * Starting at 0x40c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      var s2 := Dup12(s1);
      var s3 := Swap2(s2);
      var s4 := Dup14(s3);
      var s5 := Swap5(s4);
      var s6 := Swap4(s5);
      var s7 := Dup9(s6);
      var s8 := Swap5(s7);
      var s9 := Push2(s8, 0x0442);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s10, gas - 1)
      else
        ExecuteFromCFGNode_s113(s10, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 56
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Push2(s4, 0x0430);
      var s6 := Push2(s5, 0x043d);
      var s7 := Swap6(s6);
      var s8 := Swap5(s7);
      var s9 := Swap3(s8);
      var s10 := Push2(s9, 0x0437);
      var s11 := Swap5(s10);
      assert s11.Peek(2) == 0x430;
      assert s11.Peek(5) == 0x437;
      assert s11.Peek(7) == 0x43d;
      var s12 := And(s11);
      var s13 := Dup1(s12);
      var s14 := Swap4(s13);
      var s15 := Push2(s14, 0x07e8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s16, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 113
    * Starting at 0x7e8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x430

    requires s0.stack[5] == 0x437

    requires s0.stack[7] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x430;
      assert s1.Peek(5) == 0x437;
      assert s1.Peek(7) == 0x43d;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x07fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s8, gas - 1)
      else
        ExecuteFromCFGNode_s115(s8, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 114
    * Starting at 0x7f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x430

    requires s0.stack[5] == 0x437

    requires s0.stack[7] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(3) == 0x430;
      assert s1.Peek(6) == 0x437;
      assert s1.Peek(8) == 0x43d;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s8, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 57
    * Starting at 0x430
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x430 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x437

    requires s0.stack[5] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x437;
      assert s1.Peek(5) == 0x43d;
      var s2 := MStore(s1);
      var s3 := Dup12(s2);
      var s4 := Push2(s3, 0x07e8);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s5, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 113
    * Starting at 0x7e8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x437

    requires s0.stack[4] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x437;
      assert s1.Peek(4) == 0x43d;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Dup3(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x07fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s8, gas - 1)
      else
        ExecuteFromCFGNode_s118(s8, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 114
    * Starting at 0x7f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x437

    requires s0.stack[4] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(3) == 0x437;
      assert s1.Peek(5) == 0x43d;
      var s2 := Swap2(s1);
      var s3 := Push1(s2, 0x05);
      var s4 := Shl(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s8, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 58
    * Starting at 0x437
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x437 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x43d;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0792);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s4, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 105
    * Starting at 0x792
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x792 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x43d;
      var s2 := Push4(s1, 0xffffffff);
      var s3 := Dup1(s2);
      var s4 := Swap2(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x06be);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s10, gas - 1)
      else
        ExecuteFromCFGNode_s121(s10, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 106
    * Starting at 0x7a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(2) == 0x43d;
      var s2 := Add(s1);
      var s3 := Swap1(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s4, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 59
    * Starting at 0x43d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x03b8);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s3, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 97
    * Starting at 0x6be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x43d;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 124
    * Segment Id for this node is: 115
    * Starting at 0x7fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x437

    requires s0.stack[4] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x437;
      assert s1.Peek(4) == 0x43d;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 125
    * Segment Id for this node is: 115
    * Starting at 0x7fc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x430

    requires s0.stack[5] == 0x437

    requires s0.stack[7] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x430;
      assert s1.Peek(5) == 0x437;
      assert s1.Peek(7) == 0x43d;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x32);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 126
    * Segment Id for this node is: 60
    * Starting at 0x442
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x442 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := ReturnDataSize(s9);
      var s11 := Dup4(s10);
      var s12 := Gt(s11);
      var s13 := Push2(s12, 0x0537);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s14, gas - 1)
      else
        ExecuteFromCFGNode_s127(s14, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 61
    * Starting at 0x452
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x045c);
      var s3 := Dup2(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x0739);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s6, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 101
    * Starting at 0x739
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x739 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[2] == 0x45c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x45c;
      var s2 := Swap1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s5 := Swap2(s4);
      var s6 := Add(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x45c;
      var s12 := Lt(s11);
      var s13 := Push8(s12, 0xffffffffffffffff);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := Or(s15);
      var s17 := Push2(s16, 0x070a);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s18, gas - 1)
      else
        ExecuteFromCFGNode_s129(s18, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 102
    * Starting at 0x776
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x776 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x45c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x45c;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s3, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 62
    * Starting at 0x45c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Sub(s3);
      var s5 := SLt(s4);
      var s6 := Push2(s5, 0x02c1);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s7, gas - 1)
      else
        ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 63
    * Starting at 0x465
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x465 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup8(s0);
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0x0470);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x06ed);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s7, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 98
    * Starting at 0x6ed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x470

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x470;
      var s2 := Push2(s1, 0x0160);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup3(s8);
      var s10 := Gt(s9);
      var s11 := Or(s10);
      assert s11.Peek(2) == 0x470;
      var s12 := Push2(s11, 0x070a);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s13, gas - 1)
      else
        ExecuteFromCFGNode_s133(s13, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 99
    * Starting at 0x706
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x706 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x470

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x470;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s3, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 64
    * Starting at 0x470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0479);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x07a7);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s5, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 107
    * Starting at 0x7a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x479

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x479;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s169(s10, gas - 1)
      else
        ExecuteFromCFGNode_s136(s10, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 108
    * Starting at 0x7c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x479

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s1, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 65
    * Starting at 0x479
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x479 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup3(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push2(s4, 0x0488);
      var s6 := Dup2(s5);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x07c8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s10, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 109
    * Starting at 0x7c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x488

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x488;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0xffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s168(s10, gas - 1)
      else
        ExecuteFromCFGNode_s139(s10, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 110
    * Starting at 0x7d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x488

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s1, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 66
    * Starting at 0x488
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x488 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0497);
      var s7 := Dup10(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x07c8);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s11, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 109
    * Starting at 0x7c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x497

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x497;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0xffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s10, gas - 1)
      else
        ExecuteFromCFGNode_s142(s10, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 110
    * Starting at 0x7d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x497

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s1, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 67
    * Starting at 0x497
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup10(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Push2(s6, 0x04a8);
      var s8 := Dup2(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x07c8);
      assert s11.Peek(0) == 0x7c8;
      assert s11.Peek(2) == 0x4a8;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s12, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 109
    * Starting at 0x7c8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x4a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4a8;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push4(s3, 0xffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s10, gas - 1)
      else
        ExecuteFromCFGNode_s145(s10, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 110
    * Starting at 0x7d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x4a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s1, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 68
    * Starting at 0x4a8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Push2(s6, 0x04b9);
      var s8 := Dup2(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x07d9);
      assert s11.Peek(0) == 0x7d9;
      assert s11.Peek(2) == 0x4b9;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s12, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 111
    * Starting at 0x7d9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x4b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4b9;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push2(s3, 0xffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s10, gas - 1)
      else
        ExecuteFromCFGNode_s148(s10, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 112
    * Starting at 0x7e7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x4b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s1, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 69
    * Starting at 0x4b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Swap1(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0xa0);
      var s7 := Dup1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Swap1(s10);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0xc0);
      var s16 := Dup1(s15);
      var s17 := Dup3(s16);
      var s18 := Add(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Dup2(s20);
      var s22 := IsZero(s21);
      var s23 := IsZero(s22);
      var s24 := Dup3(s23);
      var s25 := Sub(s24);
      var s26 := Push2(s25, 0x0533);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s27, gas - 1)
      else
        ExecuteFromCFGNode_s150(s27, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 70
    * Starting at 0x4d8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 14
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup13(s0);
      var s2 := Dup5(s1);
      var s3 := Dup16(s2);
      var s4 := Swap5(s3);
      var s5 := Push2(s4, 0x043d);
      var s6 := Swap(s5, 9);
      var s7 := Swap(s6, 8);
      var s8 := Swap5(s7);
      var s9 := Push2(s8, 0x0430);
      var s10 := Swap5(s9);
      var s11 := Push2(s10, 0x0437);
      assert s11.Peek(0) == 0x437;
      assert s11.Peek(6) == 0x430;
      assert s11.Peek(11) == 0x43d;
      var s12 := Swap(s11, 9);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x04f6);
      var s16 := Dup13(s15);
      var s17 := Dup3(s16);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x07a7);
      var s20 := Jump(s19);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s20, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 107
    * Starting at 0x7a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x4f6

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4f6;
      assert s1.Peek(5) == 0x430;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(10) == 0x43d;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s10, gas - 1)
      else
        ExecuteFromCFGNode_s152(s10, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 108
    * Starting at 0x7c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x4f6

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s1, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 71
    * Starting at 0x4f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x430

    requires s0.stack[7] == 0x437

    requires s0.stack[9] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x430;
      assert s1.Peek(7) == 0x437;
      assert s1.Peek(9) == 0x43d;
      var s2 := Dup13(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Dup1(s6);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(5) == 0x430;
      assert s11.Peek(8) == 0x437;
      assert s11.Peek(10) == 0x43d;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x0120);
      var s16 := Push2(s15, 0x0513);
      var s17 := Dup2(s16);
      var s18 := Dup4(s17);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x07a7);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s21, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 107
    * Starting at 0x7a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[1] == 0x513

    requires s0.stack[6] == 0x430

    requires s0.stack[9] == 0x437

    requires s0.stack[11] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x513;
      assert s1.Peek(6) == 0x430;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(11) == 0x43d;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s162(s10, gas - 1)
      else
        ExecuteFromCFGNode_s155(s10, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 108
    * Starting at 0x7c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x513

    requires s0.stack[6] == 0x430

    requires s0.stack[9] == 0x437

    requires s0.stack[11] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s1, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 72
    * Starting at 0x513
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x513 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x430;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(10) == 0x43d;
      var s2 := Swap1(s1);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0525);
      var s7 := Push2(s6, 0x0140);
      var s8 := Dup1(s7);
      var s9 := Swap3(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x07a7);
      assert s11.Peek(0) == 0x7a7;
      assert s11.Peek(2) == 0x525;
      assert s11.Peek(6) == 0x430;
      assert s11.Peek(9) == 0x437;
      assert s11.Peek(11) == 0x43d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s157(s12, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 107
    * Starting at 0x7a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x525

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x525;
      assert s1.Peek(5) == 0x430;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(10) == 0x43d;
      var s2 := MLoad(s1);
      var s3 := Swap1(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := And(s5);
      var s7 := Dup3(s6);
      var s8 := Sub(s7);
      var s9 := Push2(s8, 0x06a3);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s10, gas - 1)
      else
        ExecuteFromCFGNode_s158(s10, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 108
    * Starting at 0x7c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x525

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s1, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 73
    * Starting at 0x525
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x525 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[4] == 0x430

    requires s0.stack[7] == 0x437

    requires s0.stack[9] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x430;
      assert s1.Peek(7) == 0x437;
      assert s1.Peek(9) == 0x43d;
      var s2 := Swap1(s1);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Swap5(s5);
      var s7 := Pop(s6);
      var s8 := Swap3(s7);
      var s9 := Swap5(s8);
      var s10 := Swap6(s9);
      var s11 := Push2(s10, 0x0418);
      assert s11.Peek(0) == 0x418;
      assert s11.Peek(1) == 0x43d;
      assert s11.Peek(2) == 0x430;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s12, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 56
    * Starting at 0x418
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x418 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x43d

    requires s0.stack[1] == 0x430

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x43d;
      assert s1.Peek(1) == 0x430;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Push2(s4, 0x0430);
      var s6 := Push2(s5, 0x043d);
      var s7 := Swap6(s6);
      var s8 := Swap5(s7);
      var s9 := Swap3(s8);
      var s10 := Push2(s9, 0x0437);
      var s11 := Swap5(s10);
      assert s11.Peek(2) == 0x430;
      assert s11.Peek(5) == 0x437;
      assert s11.Peek(7) == 0x43d;
      var s12 := And(s11);
      var s13 := Dup1(s12);
      var s14 := Swap4(s13);
      var s15 := Push2(s14, 0x07e8);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s16, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x525

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x525;
      assert s1.Peek(5) == 0x430;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(10) == 0x43d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 162
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x513

    requires s0.stack[6] == 0x430

    requires s0.stack[9] == 0x437

    requires s0.stack[11] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x513;
      assert s1.Peek(6) == 0x430;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(11) == 0x43d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 163
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x4f6

    requires s0.stack[5] == 0x430

    requires s0.stack[8] == 0x437

    requires s0.stack[10] == 0x43d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4f6;
      assert s1.Peek(5) == 0x430;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(10) == 0x43d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 164
    * Segment Id for this node is: 74
    * Starting at 0x533
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x533 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup8(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 165
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x4b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4b9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 166
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x4a8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4a8;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 167
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x497

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x497;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 168
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x488

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x488;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 169
    * Segment Id for this node is: 94
    * Starting at 0x6a3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x479

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x479;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 170
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x470

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x470;
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

  /** Node 171
    * Segment Id for this node is: 38
    * Starting at 0x2c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup5(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 172
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[1] == 0x45c

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x45c;
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

  /** Node 173
    * Segment Id for this node is: 75
    * Starting at 0x537
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x537 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := ReturnDataSize(s2);
      var s4 := Push2(s3, 0x0452);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s127(s5, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 76
    * Starting at 0x53e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup10(s1);
      var s3 := MLoad(s2);
      var s4 := ReturnDataSize(s3);
      var s5 := Dup9(s4);
      var s6 := Dup3(s5);
      var s7 := ReturnDataCopy(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Swap1(s8);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 175
    * Segment Id for this node is: 97
    * Starting at 0x6be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x3cd

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3cd;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 176
    * Segment Id for this node is: 77
    * Starting at 0x548
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x548 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup9(s1);
      var s3 := Dup6(s2);
      var s4 := Dup12(s3);
      var s5 := Dup7(s4);
      var s6 := Dup15(s5);
      var s7 := Dup12(s6);
      var s8 := Dup1(s7);
      var s9 := MLoad(s8);
      var s10 := Swap5(s9);
      var s11 := Push1(s10, 0x20);
      var s12 := Swap2(s11);
      var s13 := Dup3(s12);
      var s14 := Dup8(s13);
      var s15 := Add(s14);
      var s16 := Swap4(s15);
      var s17 := Dup4(s16);
      var s18 := Dup9(s17);
      var s19 := MStore(s18);
      var s20 := Dup7(s19);
      var s21 := MLoad(s20);
      var s22 := Dup1(s21);
      var s23 := Swap6(s22);
      var s24 := MStore(s23);
      var s25 := Dup4(s24);
      var s26 := Dup3(s25);
      var s27 := Dup10(s26);
      var s28 := Add(s27);
      var s29 := Swap(s28, 8);
      var s30 := Add(s29);
      var s31 := Swap6(s30);
      var s32 := Swap3(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s177(s32, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 78
    * Starting at 0x569
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x569 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup6(s1);
      var s3 := Dup5(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0576);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s6, gas - 1)
      else
        ExecuteFromCFGNode_s178(s6, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 79
    * Starting at 0x571
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x571 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup9(s0);
      var s2 := Dup9(s1);
      var s3 := Sub(s2);
      var s4 := Dup10(s3);
      var s5 := Return(s4);
      // Segment is terminal (Revert, Stop or Return)
      s5
  }

  /** Node 179
    * Segment Id for this node is: 80
    * Starting at 0x576
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x576 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup7(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := MLoad(s4);
      var s6 := Dup4(s5);
      var s7 := And(s6);
      var s8 := Dup10(s7);
      var s9 := MStore(s8);
      var s10 := Dup1(s9);
      var s11 := Dup7(s10);
      var s12 := Add(s11);
      var s13 := MLoad(s12);
      var s14 := Dup12(s13);
      var s15 := And(s14);
      var s16 := Dup10(s15);
      var s17 := Dup8(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Dup1(s19);
      var s21 := Dup5(s20);
      var s22 := Add(s21);
      var s23 := MLoad(s22);
      var s24 := Dup12(s23);
      var s25 := And(s24);
      var s26 := Dup10(s25);
      var s27 := Dup6(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x60);
      var s31 := Dup1(s30);
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MLoad(s33);
      var s35 := Dup13(s34);
      var s36 := And(s35);
      var s37 := Swap1(s36);
      var s38 := Dup11(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := Push1(s40, 0x80);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s41, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 81
    * Starting at 0x5a1
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0xffff);
      var s6 := And(s5);
      var s7 := Swap1(s6);
      var s8 := Dup11(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0xa0);
      var s12 := Dup1(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Dup11(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0xc0);
      var s21 := Dup1(s20);
      var s22 := Dup3(s21);
      var s23 := Add(s22);
      var s24 := MLoad(s23);
      var s25 := IsZero(s24);
      var s26 := IsZero(s25);
      var s27 := Swap1(s26);
      var s28 := Dup11(s27);
      var s29 := Add(s28);
      var s30 := MStore(s29);
      var s31 := Dup1(s30);
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MLoad(s33);
      var s35 := Dup4(s34);
      var s36 := And(s35);
      var s37 := Dup10(s36);
      var s38 := Dup4(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := Push2(s40, 0x0100);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s181(s41, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 82
    * Starting at 0x5d0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Dup11(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push2(s8, 0x0120);
      var s10 := Dup1(s9);
      var s11 := Dup3(s10);
      var s12 := Add(s11);
      var s13 := MLoad(s12);
      var s14 := Dup5(s13);
      var s15 := And(s14);
      var s16 := Swap1(s15);
      var s17 := Dup11(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Push2(s19, 0x0140);
      var s21 := Swap1(s20);
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := MLoad(s23);
      var s25 := Dup4(s24);
      var s26 := And(s25);
      var s27 := Swap1(s26);
      var s28 := Dup10(s27);
      var s29 := Add(s28);
      var s30 := MStore(s29);
      var s31 := Push2(s30, 0x0160);
      var s32 := Swap1(s31);
      var s33 := Swap(s32, 8);
      var s34 := Add(s33);
      var s35 := Swap7(s34);
      var s36 := Swap6(s35);
      var s37 := Dup5(s36);
      var s38 := Add(s37);
      var s39 := Swap6(s38);
      var s40 := Push1(s39, 0x01);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s182(s41, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 83
    * Starting at 0x600
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap4(s0);
      var s2 := Add(s1);
      var s3 := Swap3(s2);
      var s4 := Push2(s3, 0x0569);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s5, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 84
    * Starting at 0x607
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x607 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := Swap1(s2);
      var s4 := Dup6(s3);
      var s5 := Swap(s4, 10);
      var s6 := Swap7(s5);
      var s7 := Swap(s6, 10);
      var s8 := MLoad(s7);
      var s9 := Push2(s8, 0x0618);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x06ed);
      assert s11.Peek(0) == 0x6ed;
      assert s11.Peek(2) == 0x618;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s12, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 98
    * Starting at 0x6ed
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x618

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x618;
      var s2 := Push2(s1, 0x0160);
      var s3 := Dup2(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Dup2(s5);
      var s7 := Lt(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup3(s8);
      var s10 := Gt(s9);
      var s11 := Or(s10);
      assert s11.Peek(2) == 0x618;
      var s12 := Push2(s11, 0x070a);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s188(s13, gas - 1)
      else
        ExecuteFromCFGNode_s185(s13, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 99
    * Starting at 0x706
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x706 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x618

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x618;
      var s2 := MStore(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s3, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 85
    * Starting at 0x618
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x618 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup11(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Dup3(s4);
      var s6 := Dup12(s5);
      var s7 := Dup2(s6);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Dup12(s10);
      var s12 := Dup9(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Dup12(s15);
      var s17 := Push1(s16, 0x60);
      var s18 := Dup4(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Dup12(s20);
      var s22 := Push1(s21, 0x80);
      var s23 := Dup4(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Dup12(s25);
      var s27 := Push1(s26, 0xa0);
      var s28 := Dup4(s27);
      var s29 := Add(s28);
      var s30 := MStore(s29);
      var s31 := Dup12(s30);
      var s32 := Push1(s31, 0xc0);
      var s33 := Dup4(s32);
      var s34 := Add(s33);
      var s35 := MStore(s34);
      var s36 := Dup12(s35);
      var s37 := Dup7(s36);
      var s38 := Dup4(s37);
      var s39 := Add(s38);
      var s40 := MStore(s39);
      var s41 := Dup12(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s187(s41, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 86
    * Starting at 0x645
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 13
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x645 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      var s2 := Dup4(s1);
      var s3 := Add(s2);
      var s4 := MStore(s3);
      var s5 := Dup12(s4);
      var s6 := Push2(s5, 0x0120);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := MStore(s8);
      var s10 := Dup12(s9);
      var s11 := Push2(s10, 0x0140);
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup3(s14);
      var s16 := Dup12(s15);
      var s17 := Add(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Add(s19);
      var s21 := Swap(s20, 8);
      var s22 := Swap5(s21);
      var s23 := Swap(s22, 8);
      var s24 := Push2(s23, 0x0372);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s25, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x618

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x618;
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

  /** Node 189
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x36f;
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

  /** Node 190
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x367

    requires s0.stack[3] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x367;
      assert s1.Peek(3) == 0x36f;
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

  /** Node 191
    * Segment Id for this node is: 100
    * Starting at 0x70a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x35a

    requires s0.stack[2] == 0x36f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x35a;
      assert s1.Peek(2) == 0x36f;
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

  /** Node 192
    * Segment Id for this node is: 97
    * Starting at 0x6be
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x32b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x32b;
      var s2 := Push32(s1, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      var s3 := Push1(s2, 0x00);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x11);
      var s6 := Push1(s5, 0x04);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x24);
      var s9 := Push1(s8, 0x00);
      var s10 := Revert(s9);
      // Segment is terminal (Revert, Stop or Return)
      s10
  }

  /** Node 193
    * Segment Id for this node is: 87
    * Starting at 0x666
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x666 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup7(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 194
    * Segment Id for this node is: 88
    * Starting at 0x66a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup4(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 195
    * Segment Id for this node is: 89
    * Starting at 0x66e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
