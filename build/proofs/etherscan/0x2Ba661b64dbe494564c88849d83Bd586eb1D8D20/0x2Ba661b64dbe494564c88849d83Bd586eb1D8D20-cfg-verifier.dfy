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
      var s6 := Push2(s5, 0x00f5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s262(s7, gas - 1)
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
      var s6 := Push4(s5, 0x715018a6);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x0097);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s9, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s84(s5, gas - 1)
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
      var s2 := Push4(s1, 0xa9059cbb);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01f1);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s46(s5, gas - 1)
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
      var s2 := Push4(s1, 0xdd62ed3e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0204);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf2fde38b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x023d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s13(s5, gas - 1)
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
      var s2 := Push4(s1, 0xffa1ad74);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0250);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s10(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := Push1(s0, 0x00);
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 10
    * Segment Id for this node is: 52
    * Starting at 0x250
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x013f);
      var s3 := Push1(s2, 0x01);
      var s4 := Dup2(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 32
    * Starting at 0x13f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13f;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x010f);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s10, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 27
    * Starting at 0x10f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13f;
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

  /** Node 13
    * Segment Id for this node is: 50
    * Starting at 0x23d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01b9);
      var s3 := Push2(s2, 0x024b);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0896);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s7, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 110
    * Starting at 0x896
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x896 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x24b

    requires s0.stack[3] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24b;
      assert s1.Peek(3) == 0x1b9;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08a7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s16(s10, gas - 1)
      else
        ExecuteFromCFGNode_s15(s10, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 111
    * Starting at 0x8a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x24b

    requires s0.stack[4] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x24b;
      assert s1.Peek(5) == 0x1b9;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 16
    * Segment Id for this node is: 112
    * Starting at 0x8a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x24b

    requires s0.stack[4] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x24b;
      assert s1.Peek(4) == 0x1b9;
      var s2 := Push2(s1, 0x054c);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x54c

    requires s0.stack[5] == 0x24b

    requires s0.stack[6] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x54c;
      assert s1.Peek(5) == 0x24b;
      assert s1.Peek(6) == 0x1b9;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x54c;
      assert s11.Peek(8) == 0x24b;
      assert s11.Peek(9) == 0x1b9;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s14, gas - 1)
      else
        ExecuteFromCFGNode_s18(s14, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x24b

    requires s0.stack[7] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x54c;
      assert s1.Peek(7) == 0x24b;
      assert s1.Peek(8) == 0x1b9;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 19
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x24b

    requires s0.stack[7] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x54c;
      assert s1.Peek(6) == 0x24b;
      assert s1.Peek(7) == 0x1b9;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s5, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 86
    * Starting at 0x54c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x24b

    requires s0.stack[5] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x24b;
      assert s1.Peek(5) == 0x1b9;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s7, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 51
    * Starting at 0x24b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b9;
      var s2 := Push2(s1, 0x0475);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 79
    * Starting at 0x475
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x475 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b9;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(2) == 0x1b9;
      var s12 := Push2(s11, 0x04cf);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s13, gas - 1)
      else
        ExecuteFromCFGNode_s23(s13, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 80
    * Starting at 0x488
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x488 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1b9;
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
      assert s11.Peek(4) == 0x1b9;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(5) == 0x1b9;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      var s26 := Push2(s25, 0x03f5);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s27, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b9;
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

  /** Node 25
    * Segment Id for this node is: 81
    * Starting at 0x4cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b9;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0534);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s10, gas - 1)
      else
        ExecuteFromCFGNode_s26(s10, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 82
    * Starting at 0x4de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x1b9;
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
      assert s11.Peek(4) == 0x1b9;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x4f776e61626c653a206e6577206f776e657220697320746865207a65726f2061);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x1b9;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 6, 0x646472657373);
      var s24 := Push1(s23, 0xd0);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x1b9;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s24(s33, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 83
    * Starting at 0x534
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x534 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b9;
      var s2 := Push2(s1, 0x053d);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x082a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s5, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 106
    * Starting at 0x82a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x53d

    requires s0.stack[3] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x53d;
      assert s1.Peek(3) == 0x1b9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x53d;
      assert s11.Peek(8) == 0x1b9;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Dup4(s18);
      var s20 := And(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x53d;
      assert s21.Peek(9) == 0x1b9;
      var s22 := Or(s21);
      var s23 := Dup5(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := And(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(5) == 0x53d;
      assert s31.Peek(7) == 0x1b9;
      var s32 := Dup4(s31);
      var s33 := Swap2(s32);
      var s34 := Push32(s33, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Log3(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s40, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 84
    * Starting at 0x53d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b9;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s3, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 41
    * Starting at 0x1b9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b9 as nat
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

  /** Node 31
    * Segment Id for this node is: 48
    * Starting at 0x204
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x204 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x013f);
      var s3 := Push2(s2, 0x0212);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x08b0);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s7, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 113
    * Starting at 0x8b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x212

    requires s0.stack[3] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x212;
      assert s1.Peek(3) == 0x13f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x08c2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s11, gas - 1)
      else
        ExecuteFromCFGNode_s33(s11, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 114
    * Starting at 0x8bf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x212

    requires s0.stack[5] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(5) == 0x212;
      assert s1.Peek(6) == 0x13f;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 34
    * Segment Id for this node is: 115
    * Starting at 0x8c2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x212

    requires s0.stack[5] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x212;
      assert s1.Peek(5) == 0x13f;
      var s2 := Push2(s1, 0x08cb);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s5, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x8cb

    requires s0.stack[6] == 0x212

    requires s0.stack[7] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8cb;
      assert s1.Peek(6) == 0x212;
      assert s1.Peek(7) == 0x13f;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x8cb;
      assert s11.Peek(9) == 0x212;
      assert s11.Peek(10) == 0x13f;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s14, gas - 1)
      else
        ExecuteFromCFGNode_s36(s14, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x8cb

    requires s0.stack[7] == 0x212

    requires s0.stack[8] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x8cb;
      assert s1.Peek(8) == 0x212;
      assert s1.Peek(9) == 0x13f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 37
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x8cb

    requires s0.stack[7] == 0x212

    requires s0.stack[8] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8cb;
      assert s1.Peek(7) == 0x212;
      assert s1.Peek(8) == 0x13f;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s5, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 116
    * Starting at 0x8cb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x212

    requires s0.stack[6] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x212;
      assert s1.Peek(6) == 0x13f;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x08d9);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x087a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s9, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x8d9

    requires s0.stack[6] == 0x212

    requires s0.stack[7] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8d9;
      assert s1.Peek(6) == 0x212;
      assert s1.Peek(7) == 0x13f;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x8d9;
      assert s11.Peek(9) == 0x212;
      assert s11.Peek(10) == 0x13f;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s14, gas - 1)
      else
        ExecuteFromCFGNode_s40(s14, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x8d9

    requires s0.stack[7] == 0x212

    requires s0.stack[8] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x8d9;
      assert s1.Peek(8) == 0x212;
      assert s1.Peek(9) == 0x13f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 41
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x8d9

    requires s0.stack[7] == 0x212

    requires s0.stack[8] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8d9;
      assert s1.Peek(7) == 0x212;
      assert s1.Peek(8) == 0x13f;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s5, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 117
    * Starting at 0x8d9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x212

    requires s0.stack[6] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x212;
      assert s1.Peek(6) == 0x13f;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap3(s3);
      var s5 := Pop(s4);
      var s6 := Swap3(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s9, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 49
    * Starting at 0x212
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x212 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x13f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Swap2(s6);
      var s8 := Dup3(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(4) == 0x13f;
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
      assert s21.Peek(7) == 0x13f;
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
      assert s31.Peek(4) == 0x13f;
      var s32 := MStore(s31);
      var s33 := Keccak256(s32);
      var s34 := SLoad(s33);
      var s35 := Swap1(s34);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s36, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 32
    * Starting at 0x13f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f as nat
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
      var s9 := Push2(s8, 0x010f);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s10, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 27
    * Starting at 0x10f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10f as nat
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

  /** Node 46
    * Segment Id for this node is: 46
    * Starting at 0x1f1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x012b);
      var s3 := Push2(s2, 0x01ff);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x091d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 123
    * Starting at 0x91d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ff

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ff;
      assert s1.Peek(3) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x092f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s49(s11, gas - 1)
      else
        ExecuteFromCFGNode_s48(s11, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 124
    * Starting at 0x92c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ff

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x1ff;
      assert s1.Peek(6) == 0x12b;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 49
    * Segment Id for this node is: 125
    * Starting at 0x92f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ff

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1ff;
      assert s1.Peek(5) == 0x12b;
      var s2 := Push2(s1, 0x0938);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x938

    requires s0.stack[6] == 0x1ff

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x938;
      assert s1.Peek(6) == 0x1ff;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x938;
      assert s11.Peek(9) == 0x1ff;
      assert s11.Peek(10) == 0x12b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s14, gas - 1)
      else
        ExecuteFromCFGNode_s51(s14, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x1ff

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x938;
      assert s1.Peek(8) == 0x1ff;
      assert s1.Peek(9) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 52
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x1ff

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x938;
      assert s1.Peek(7) == 0x1ff;
      assert s1.Peek(8) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s5, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 126
    * Starting at 0x938
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1ff

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ff;
      assert s1.Peek(6) == 0x12b;
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
      assert s11.Peek(1) == 0x1ff;
      assert s11.Peek(4) == 0x12b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s13, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 47
    * Starting at 0x1ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push2(s1, 0x0468);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s55(s3, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 78
    * Starting at 0x468
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x468 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f7);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0678);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s8, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 94
    * Starting at 0x678
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x678 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06dc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s59(s10, gas - 1)
      else
        ExecuteFromCFGNode_s57(s10, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 95
    * Starting at 0x687
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x687 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
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
      assert s11.Peek(6) == 0x2f7;
      assert s11.Peek(10) == 0x12b;
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
      assert s21.Peek(6) == 0x2f7;
      assert s21.Peek(10) == 0x12b;
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
      assert s31.Peek(4) == 0x2f7;
      assert s31.Peek(8) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s33, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2f7

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
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

  /** Node 59
    * Segment Id for this node is: 96
    * Starting at 0x6dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x073e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s10, gas - 1)
      else
        ExecuteFromCFGNode_s60(s10, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 97
    * Starting at 0x6eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
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
      assert s11.Peek(6) == 0x2f7;
      assert s11.Peek(10) == 0x12b;
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
      assert s21.Peek(6) == 0x2f7;
      assert s21.Peek(10) == 0x12b;
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
      assert s31.Peek(4) == 0x2f7;
      assert s31.Peek(8) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s33, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 98
    * Starting at 0x73e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push2(s1, 0x077b);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(3) == 0x77b;
      assert s11.Peek(7) == 0x2f7;
      assert s11.Peek(11) == 0x12b;
      var s12 := Push1(s11, 0x26);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x09f9);
      var s18 := Push1(s17, 0x26);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(3) == 0x77b;
      assert s21.Peek(7) == 0x2f7;
      assert s21.Peek(11) == 0x12b;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0xa0);
      var s24 := Shl(s23);
      var s25 := Sub(s24);
      var s26 := Dup7(s25);
      var s27 := And(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Swap1(s28);
      var s30 := Dup2(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x77b;
      assert s31.Peek(7) == 0x2f7;
      assert s31.Peek(11) == 0x12b;
      var s32 := Push1(s31, 0x01);
      var s33 := Push1(s32, 0x20);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := Swap1(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap2(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x07fe);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s41, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 99
    * Starting at 0x77a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x7fe

    requires s0.stack[4] == 0x77b

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s1, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 103
    * Starting at 0x7fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x77b

    requires s0.stack[7] == 0x2f7

    requires s0.stack[11] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x77b;
      assert s1.Peek(7) == 0x2f7;
      assert s1.Peek(11) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0822);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s9, gas - 1)
      else
        ExecuteFromCFGNode_s64(s9, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 104
    * Starting at 0x80a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x77b

    requires s0.stack[9] == 0x2f7

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x77b;
      assert s1.Peek(10) == 0x2f7;
      assert s1.Peek(14) == 0x12b;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f5);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f5;
      assert s11.Peek(7) == 0x77b;
      assert s11.Peek(11) == 0x2f7;
      assert s11.Peek(15) == 0x12b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0946);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s14, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 127
    * Starting at 0x946
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x946 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x3f5

    requires s0.stack[7] == 0x77b

    requires s0.stack[11] == 0x2f7

    requires s0.stack[15] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f5;
      assert s1.Peek(7) == 0x77b;
      assert s1.Peek(11) == 0x2f7;
      assert s1.Peek(15) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x77b;
      assert s11.Peek(17) == 0x2f7;
      assert s11.Peek(21) == 0x12b;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s66(s14, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 128
    * Starting at 0x956
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x956 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x2f7

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x77b;
      assert s1.Peek(15) == 0x2f7;
      assert s1.Peek(19) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0972);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s7, gas - 1)
      else
        ExecuteFromCFGNode_s67(s7, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 129
    * Starting at 0x95f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x2f7

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x77b;
      assert s1.Peek(16) == 0x2f7;
      assert s1.Peek(20) == 0x12b;
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
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x77b;
      assert s11.Peek(17) == 0x2f7;
      assert s11.Peek(21) == 0x12b;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0956);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s16, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 130
    * Starting at 0x972
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x2f7

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x77b;
      assert s1.Peek(15) == 0x2f7;
      assert s1.Peek(19) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0983);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s70(s7, gas - 1)
      else
        ExecuteFromCFGNode_s69(s7, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 131
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x2f7

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x77b;
      assert s1.Peek(16) == 0x2f7;
      assert s1.Peek(20) == 0x12b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s70(s7, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 132
    * Starting at 0x983
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x2f7

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x77b;
      assert s1.Peek(15) == 0x2f7;
      assert s1.Peek(19) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x3f5;
      assert s11.Peek(9) == 0x77b;
      assert s11.Peek(13) == 0x2f7;
      assert s11.Peek(17) == 0x12b;
      var s12 := Push1(s11, 0x40);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s19, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x77b

    requires s0.stack[9] == 0x2f7

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x77b;
      assert s1.Peek(9) == 0x2f7;
      assert s1.Peek(13) == 0x12b;
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
    * Segment Id for this node is: 105
    * Starting at 0x822
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x822 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x77b

    requires s0.stack[9] == 0x2f7

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x77b;
      assert s1.Peek(9) == 0x2f7;
      assert s1.Peek(13) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s8, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 100
    * Starting at 0x77b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2f7

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x2f7;
      assert s11.Peek(11) == 0x12b;
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
      assert s21.Peek(8) == 0x2f7;
      assert s21.Peek(12) == 0x12b;
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
      assert s31.Peek(4) == 0x2f7;
      assert s31.Peek(8) == 0x12b;
      var s32 := Push2(s31, 0x07aa);
      var s33 := Swap1(s32);
      var s34 := Dup3(s33);
      var s35 := Push2(s34, 0x0540);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s36, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 85
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x7aa

    requires s0.stack[6] == 0x2f7

    requires s0.stack[10] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7aa;
      assert s1.Peek(6) == 0x2f7;
      assert s1.Peek(10) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x054c);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0999);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s7, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 133
    * Starting at 0x999
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x999 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x7aa

    requires s0.stack[10] == 0x2f7

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x54c;
      assert s1.Peek(6) == 0x7aa;
      assert s1.Peek(10) == 0x2f7;
      assert s1.Peek(14) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s9, gas - 1)
      else
        ExecuteFromCFGNode_s76(s9, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 134
    * Starting at 0x9a5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x54c

    requires s0.stack[7] == 0x7aa

    requires s0.stack[11] == 0x2f7

    requires s0.stack[15] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x54c;
      assert s1.Peek(8) == 0x7aa;
      assert s1.Peek(12) == 0x2f7;
      assert s1.Peek(16) == 0x12b;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Dup2(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 77
    * Segment Id for this node is: 135
    * Starting at 0x9b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x54c

    requires s0.stack[7] == 0x7aa

    requires s0.stack[11] == 0x2f7

    requires s0.stack[15] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x54c;
      assert s1.Peek(7) == 0x7aa;
      assert s1.Peek(11) == 0x2f7;
      assert s1.Peek(15) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s5, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 86
    * Starting at 0x54c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x7aa

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7aa;
      assert s1.Peek(8) == 0x2f7;
      assert s1.Peek(12) == 0x12b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s7, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 101
    * Starting at 0x7aa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x2f7

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup5(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x2f7;
      assert s11.Peek(12) == 0x12b;
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
      assert s21.Peek(8) == 0x2f7;
      assert s21.Peek(12) == 0x12b;
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
      assert s31.Peek(6) == 0x2f7;
      assert s31.Peek(10) == 0x12b;
      var s32 := Push32(s31, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x066b);
      var s35 := Swap1(s34);
      var s36 := Dup6(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s41, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 102
    * Starting at 0x7fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x66b

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s1, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 93
    * Starting at 0x66b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[7] == 0x2f7

    requires s0.stack[11] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2f7;
      assert s1.Peek(11) == 0x12b;
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
      assert s11.Peek(0) == 0x2f7;
      assert s11.Peek(4) == 0x12b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s12, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 63
    * Starting at 0x2f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s8, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 30
    * Starting at 0x12b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b as nat
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
      var s11 := Push2(s10, 0x010f);
      assert s11.Peek(0) == 0x10f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s12, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 10
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x715018a6);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x01b1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s6, gas - 1)
      else
        ExecuteFromCFGNode_s85(s6, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01bb);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s5, gas - 1)
      else
        ExecuteFromCFGNode_s86(s5, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x95d89b41);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01d6);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s5, gas - 1)
      else
        ExecuteFromCFGNode_s87(s5, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa457c2d7);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01de);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s5, gas - 1)
      else
        ExecuteFromCFGNode_s88(s5, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 14
    * Starting at 0x93
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
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

  /** Node 89
    * Segment Id for this node is: 44
    * Starting at 0x1de
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x012b);
      var s3 := Push2(s2, 0x01ec);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x091d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s7, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 123
    * Starting at 0x91d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1ec

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1ec;
      assert s1.Peek(3) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x092f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s11, gas - 1)
      else
        ExecuteFromCFGNode_s91(s11, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 124
    * Starting at 0x92c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ec

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x1ec;
      assert s1.Peek(6) == 0x12b;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 92
    * Segment Id for this node is: 125
    * Starting at 0x92f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1ec

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1ec;
      assert s1.Peek(5) == 0x12b;
      var s2 := Push2(s1, 0x0938);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s5, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x938

    requires s0.stack[6] == 0x1ec

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x938;
      assert s1.Peek(6) == 0x1ec;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x938;
      assert s11.Peek(9) == 0x1ec;
      assert s11.Peek(10) == 0x12b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s14, gas - 1)
      else
        ExecuteFromCFGNode_s94(s14, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x1ec

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x938;
      assert s1.Peek(8) == 0x1ec;
      assert s1.Peek(9) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 95
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x1ec

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x938;
      assert s1.Peek(7) == 0x1ec;
      assert s1.Peek(8) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s5, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 126
    * Starting at 0x938
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1ec

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1ec;
      assert s1.Peek(6) == 0x12b;
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
      assert s11.Peek(1) == 0x1ec;
      assert s11.Peek(4) == 0x12b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s13, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 45
    * Starting at 0x1ec
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push2(s1, 0x0419);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 76
    * Starting at 0x419
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 14
    * Net Stack Effect: +14
    * Net Capacity Effect: -14
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x419 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f7);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x035a);
      var s7 := Dup6(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MLoad(s8);
      var s10 := Dup1(s9);
      var s11 := Push1(s10, 0x60);
      assert s11.Peek(4) == 0x35a;
      assert s11.Peek(7) == 0x2f7;
      assert s11.Peek(11) == 0x12b;
      var s12 := Add(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := Push1(s15, 0x25);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0a47);
      assert s21.Peek(4) == 0x35a;
      assert s21.Peek(7) == 0x2f7;
      assert s21.Peek(11) == 0x12b;
      var s22 := Push1(s21, 0x25);
      var s23 := Swap2(s22);
      var s24 := CodeCopy(s23);
      var s25 := Caller(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Swap1(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x02);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(5) == 0x35a;
      assert s31.Peek(8) == 0x2f7;
      assert s31.Peek(12) == 0x12b;
      var s32 := Swap1(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := Dup1(s35);
      var s37 := Dup4(s36);
      var s38 := Keccak256(s37);
      var s39 := Push1(s38, 0x01);
      var s40 := Push1(s39, 0x01);
      var s41 := Push1(s40, 0xa0);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s99(s41, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 77
    * Starting at 0x456
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 16
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x456 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[9] == 0x35a

    requires s0.stack[12] == 0x2f7

    requires s0.stack[16] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Shl(s0);
      assert s1.Peek(8) == 0x35a;
      assert s1.Peek(11) == 0x2f7;
      assert s1.Peek(15) == 0x12b;
      var s2 := Sub(s1);
      var s3 := Dup14(s2);
      var s4 := And(s3);
      var s5 := Dup5(s4);
      var s6 := MStore(s5);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := MStore(s8);
      var s10 := Swap1(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(3) == 0x35a;
      assert s11.Peek(6) == 0x2f7;
      assert s11.Peek(10) == 0x12b;
      var s12 := SLoad(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x07fe);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s16, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 103
    * Starting at 0x7fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x35a

    requires s0.stack[6] == 0x2f7

    requires s0.stack[10] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35a;
      assert s1.Peek(6) == 0x2f7;
      assert s1.Peek(10) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0822);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s109(s9, gas - 1)
      else
        ExecuteFromCFGNode_s101(s9, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 104
    * Starting at 0x80a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x35a

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x35a;
      assert s1.Peek(9) == 0x2f7;
      assert s1.Peek(13) == 0x12b;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f5);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f5;
      assert s11.Peek(7) == 0x35a;
      assert s11.Peek(10) == 0x2f7;
      assert s11.Peek(14) == 0x12b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0946);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s14, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 127
    * Starting at 0x946
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x946 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x3f5

    requires s0.stack[7] == 0x35a

    requires s0.stack[10] == 0x2f7

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f5;
      assert s1.Peek(7) == 0x35a;
      assert s1.Peek(10) == 0x2f7;
      assert s1.Peek(14) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x35a;
      assert s11.Peek(16) == 0x2f7;
      assert s11.Peek(20) == 0x12b;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s103(s14, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 128
    * Starting at 0x956
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x956 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x2f7

    requires s0.stack[18] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(14) == 0x2f7;
      assert s1.Peek(18) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0972);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s7, gas - 1)
      else
        ExecuteFromCFGNode_s104(s7, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 129
    * Starting at 0x95f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x2f7

    requires s0.stack[18] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x35a;
      assert s1.Peek(15) == 0x2f7;
      assert s1.Peek(19) == 0x12b;
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
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x35a;
      assert s11.Peek(16) == 0x2f7;
      assert s11.Peek(20) == 0x12b;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0956);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s16, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 130
    * Starting at 0x972
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x2f7

    requires s0.stack[18] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(14) == 0x2f7;
      assert s1.Peek(18) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0983);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s107(s7, gas - 1)
      else
        ExecuteFromCFGNode_s106(s7, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 131
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x2f7

    requires s0.stack[18] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x35a;
      assert s1.Peek(15) == 0x2f7;
      assert s1.Peek(19) == 0x12b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s107(s7, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 132
    * Starting at 0x983
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x2f7

    requires s0.stack[18] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(14) == 0x2f7;
      assert s1.Peek(18) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x3f5;
      assert s11.Peek(9) == 0x35a;
      assert s11.Peek(12) == 0x2f7;
      assert s11.Peek(16) == 0x12b;
      var s12 := Push1(s11, 0x40);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s19, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x35a

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x35a;
      assert s1.Peek(8) == 0x2f7;
      assert s1.Peek(12) == 0x12b;
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

  /** Node 109
    * Segment Id for this node is: 105
    * Starting at 0x822
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x822 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x35a

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x35a;
      assert s1.Peek(8) == 0x2f7;
      assert s1.Peek(12) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s8, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 67
    * Starting at 0x35a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push2(s1, 0x0553);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s3, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 87
    * Starting at 0x553
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x553 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x05b5);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s10, gas - 1)
      else
        ExecuteFromCFGNode_s112(s10, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 88
    * Starting at 0x562
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x562 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
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
      assert s11.Peek(6) == 0x2f7;
      assert s11.Peek(10) == 0x12b;
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
      assert s21.Peek(6) == 0x2f7;
      assert s21.Peek(10) == 0x12b;
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
      assert s31.Peek(4) == 0x2f7;
      assert s31.Peek(8) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s33, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 89
    * Starting at 0x5b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0616);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s115(s10, gas - 1)
      else
        ExecuteFromCFGNode_s114(s10, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 90
    * Starting at 0x5c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x2f7;
      assert s1.Peek(8) == 0x12b;
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
      assert s11.Peek(6) == 0x2f7;
      assert s11.Peek(10) == 0x12b;
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
      assert s21.Peek(6) == 0x2f7;
      assert s21.Peek(10) == 0x12b;
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
      assert s31.Peek(4) == 0x2f7;
      assert s31.Peek(8) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s33, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 91
    * Starting at 0x616
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x616 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2f7

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2f7;
      assert s1.Peek(7) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x2f7;
      assert s11.Peek(11) == 0x12b;
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
      assert s21.Peek(10) == 0x2f7;
      assert s21.Peek(14) == 0x12b;
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
      assert s31.Peek(8) == 0x2f7;
      assert s31.Peek(12) == 0x12b;
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
      ExecuteFromCFGNode_s116(s41, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 92
    * Starting at 0x646
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x646 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x2f7

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x2f7;
      assert s1.Peek(13) == 0x12b;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s81(s5, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 43
    * Starting at 0x1d6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0102);
      var s3 := Push2(s2, 0x040a);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s4, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 75
    * Starting at 0x40a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0267);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x09bd);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s9, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 136
    * Starting at 0x9bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x267

    requires s0.stack[4] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x267;
      assert s1.Peek(4) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x09d1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s11, gas - 1)
      else
        ExecuteFromCFGNode_s120(s11, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 137
    * Starting at 0x9cb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x267

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x267;
      assert s1.Peek(7) == 0x102;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s121(s5, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 138
    * Starting at 0x9d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x267

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x267;
      assert s1.Peek(6) == 0x102;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09f2);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s9, gas - 1)
      else
        ExecuteFromCFGNode_s122(s9, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 139
    * Starting at 0x9dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x267

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x267;
      assert s1.Peek(7) == 0x102;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 123
    * Segment Id for this node is: 140
    * Starting at 0x9f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x267

    requires s0.stack[6] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x267;
      assert s1.Peek(6) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 54
    * Starting at 0x267
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x267 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup1(s5);
      var s7 := Swap2(s6);
      var s8 := Div(s7);
      var s9 := Mul(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x102;
      var s12 := Push1(s11, 0x40);
      var s13 := MLoad(s12);
      var s14 := Swap1(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Push1(s16, 0x40);
      var s18 := MStore(s17);
      var s19 := Dup1(s18);
      var s20 := Swap3(s19);
      var s21 := Swap2(s20);
      assert s21.Peek(5) == 0x102;
      var s22 := Swap1(s21);
      var s23 := Dup2(s22);
      var s24 := Dup2(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x20);
      var s27 := Add(s26);
      var s28 := Dup3(s27);
      var s29 := Dup1(s28);
      var s30 := SLoad(s29);
      var s31 := Push2(s30, 0x0293);
      assert s31.Peek(0) == 0x293;
      assert s31.Peek(8) == 0x102;
      var s32 := Swap1(s31);
      var s33 := Push2(s32, 0x09bd);
      var s34 := Jump(s33);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s125(s34, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 136
    * Starting at 0x9bd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x293

    requires s0.stack[8] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x293;
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup2(s2);
      var s4 := Dup2(s3);
      var s5 := Shr(s4);
      var s6 := Swap1(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Dup1(s8);
      var s10 := Push2(s9, 0x09d1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s11, gas - 1)
      else
        ExecuteFromCFGNode_s126(s11, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 137
    * Starting at 0x9cb
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x293

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x7f);
      assert s1.Peek(4) == 0x293;
      assert s1.Peek(11) == 0x102;
      var s2 := Dup3(s1);
      var s3 := And(s2);
      var s4 := Swap2(s3);
      var s5 := Pop(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s127(s5, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 138
    * Starting at 0x9d1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x293

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x293;
      assert s1.Peek(10) == 0x102;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Lt(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09f2);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s129(s9, gas - 1)
      else
        ExecuteFromCFGNode_s128(s9, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 139
    * Starting at 0x9dd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x293

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x293;
      assert s1.Peek(11) == 0x102;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x22);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 129
    * Segment Id for this node is: 140
    * Starting at 0x9f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x293

    requires s0.stack[10] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x293;
      assert s1.Peek(10) == 0x102;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s6, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 55
    * Starting at 0x293
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x102;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x02e0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s133(s5, gas - 1)
      else
        ExecuteFromCFGNode_s131(s5, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 56
    * Starting at 0x29a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(8) == 0x102;
      var s2 := Push1(s1, 0x1f);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x02b5);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s5, gas - 1)
      else
        ExecuteFromCFGNode_s132(s5, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 57
    * Starting at 0x2a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      assert s1.Peek(8) == 0x102;
      var s2 := Dup1(s1);
      var s3 := Dup4(s2);
      var s4 := SLoad(s3);
      var s5 := Div(s4);
      var s6 := Mul(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x102;
      var s12 := Swap2(s11);
      var s13 := Push2(s12, 0x02e0);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s14, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 61
    * Starting at 0x2e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x102;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Swap1(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s10, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 26
    * Starting at 0x102
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x102 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x010f);
      var s5 := Swap2(s4);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0946);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s8, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 127
    * Starting at 0x946
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x946 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x10f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x10f;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s136(s14, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 128
    * Starting at 0x956
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x956 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0972);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s7, gas - 1)
      else
        ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 129
    * Starting at 0x95f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x10f;
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
      assert s11.Peek(8) == 0x10f;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0956);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s16, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 130
    * Starting at 0x972
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x10f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0983);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s7, gas - 1)
      else
        ExecuteFromCFGNode_s139(s7, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 131
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x10f;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s140(s7, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 132
    * Starting at 0x983
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x10f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x10f;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x10f;
      var s12 := Push1(s11, 0x40);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s19, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 58
    * Starting at 0x2b5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x102;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Push1(s8, 0x00);
      var s10 := Keccak256(s9);
      var s11 := Swap1(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s142(s11, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 59
    * Starting at 0x2c3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x102;
      var s2 := Dup2(s1);
      var s3 := SLoad(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(7) == 0x102;
      var s12 := Dup1(s11);
      var s13 := Dup4(s12);
      var s14 := Gt(s13);
      var s15 := Push2(s14, 0x02c3);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s142(s16, gas - 1)
      else
        ExecuteFromCFGNode_s143(s16, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 60
    * Starting at 0x2d7
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(8) == 0x102;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := And(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s133(s8, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 42
    * Starting at 0x1bb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1bb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := Swap1(s10);
      var s12 := Swap2(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push2(s17, 0x010f);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s19, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 40
    * Starting at 0x1b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01b9);
      var s3 := Push2(s2, 0x039f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s146(s4, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 70
    * Starting at 0x39f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b9;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Caller(s9);
      var s11 := Eq(s10);
      assert s11.Peek(1) == 0x1b9;
      var s12 := Push2(s11, 0x03fe);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s13, gas - 1)
      else
        ExecuteFromCFGNode_s147(s13, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 71
    * Starting at 0x3b2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x1b9;
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
      assert s11.Peek(3) == 0x1b9;
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Push32(s18, 0x4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572);
      var s20 := Push1(s19, 0x44);
      var s21 := Dup3(s20);
      assert s21.Peek(4) == 0x1b9;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x64);
      var s25 := Add(s24);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s148(s25, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b9;
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

  /** Node 149
    * Segment Id for this node is: 73
    * Starting at 0x3fe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b9;
      var s2 := Push2(s1, 0x0408);
      var s3 := Push1(s2, 0x00);
      var s4 := Push2(s3, 0x082a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s5, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 106
    * Starting at 0x82a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x82a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x408

    requires s0.stack[2] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x408;
      assert s1.Peek(2) == 0x1b9;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Dup4(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x408;
      assert s11.Peek(7) == 0x1b9;
      var s12 := And(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := Push1(s13, 0x01);
      var s15 := Push1(s14, 0xa0);
      var s16 := Shl(s15);
      var s17 := Sub(s16);
      var s18 := Not(s17);
      var s19 := Dup4(s18);
      var s20 := And(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(7) == 0x408;
      assert s21.Peek(8) == 0x1b9;
      var s22 := Or(s21);
      var s23 := Dup5(s22);
      var s24 := SStore(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap3(s28);
      var s30 := And(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(5) == 0x408;
      assert s31.Peek(6) == 0x1b9;
      var s32 := Dup4(s31);
      var s33 := Swap2(s32);
      var s34 := Push32(s33, 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0);
      var s35 := Swap2(s34);
      var s36 := Swap1(s35);
      var s37 := Log3(s36);
      var s38 := Pop(s37);
      var s39 := Pop(s38);
      var s40 := Jump(s39);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s40, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 74
    * Starting at 0x408
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x408 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1b9

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1b9;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s2, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 15
    * Starting at 0x97
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x23b872dd);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00d3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s245(s6, gas - 1)
      else
        ExecuteFromCFGNode_s153(s6, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x23b872dd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x014d);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s5, gas - 1)
      else
        ExecuteFromCFGNode_s154(s5, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x313ce567);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0160);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s5, gas - 1)
      else
        ExecuteFromCFGNode_s155(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x39509351);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0175);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s167(s5, gas - 1)
      else
        ExecuteFromCFGNode_s156(s5, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 19
    * Starting at 0xc4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x70a08231);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0188);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s5, gas - 1)
      else
        ExecuteFromCFGNode_s157(s5, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 20
    * Starting at 0xcf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcf as nat
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

  /** Node 158
    * Segment Id for this node is: 38
    * Starting at 0x188
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x188 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x013f);
      var s3 := Push2(s2, 0x0196);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0896);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s7, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 110
    * Starting at 0x896
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x896 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x196

    requires s0.stack[3] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x196;
      assert s1.Peek(3) == 0x13f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x08a7);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s10, gas - 1)
      else
        ExecuteFromCFGNode_s160(s10, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 111
    * Starting at 0x8a4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x196

    requires s0.stack[4] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(4) == 0x196;
      assert s1.Peek(5) == 0x13f;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 161
    * Segment Id for this node is: 112
    * Starting at 0x8a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x196

    requires s0.stack[4] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x196;
      assert s1.Peek(4) == 0x13f;
      var s2 := Push2(s1, 0x054c);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s162(s5, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x54c

    requires s0.stack[5] == 0x196

    requires s0.stack[6] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x54c;
      assert s1.Peek(5) == 0x196;
      assert s1.Peek(6) == 0x13f;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x54c;
      assert s11.Peek(8) == 0x196;
      assert s11.Peek(9) == 0x13f;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s14, gas - 1)
      else
        ExecuteFromCFGNode_s163(s14, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x196

    requires s0.stack[7] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x54c;
      assert s1.Peek(7) == 0x196;
      assert s1.Peek(8) == 0x13f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 164
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x196

    requires s0.stack[7] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x54c;
      assert s1.Peek(6) == 0x196;
      assert s1.Peek(7) == 0x13f;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s165(s5, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 86
    * Starting at 0x54c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x196

    requires s0.stack[5] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x196;
      assert s1.Peek(5) == 0x13f;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s7, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 39
    * Starting at 0x196
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x196 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x13f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x13f;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x13f;
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
      ExecuteFromCFGNode_s44(s20, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 36
    * Starting at 0x175
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x175 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x012b);
      var s3 := Push2(s2, 0x0183);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x091d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s7, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 123
    * Starting at 0x91d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x183

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x183;
      assert s1.Peek(3) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x092f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s170(s11, gas - 1)
      else
        ExecuteFromCFGNode_s169(s11, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 124
    * Starting at 0x92c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x183

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x183;
      assert s1.Peek(6) == 0x12b;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 170
    * Segment Id for this node is: 125
    * Starting at 0x92f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x183

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x183;
      assert s1.Peek(5) == 0x12b;
      var s2 := Push2(s1, 0x0938);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s5, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x938

    requires s0.stack[6] == 0x183

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x938;
      assert s1.Peek(6) == 0x183;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x938;
      assert s11.Peek(9) == 0x183;
      assert s11.Peek(10) == 0x12b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s173(s14, gas - 1)
      else
        ExecuteFromCFGNode_s172(s14, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x183

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x938;
      assert s1.Peek(8) == 0x183;
      assert s1.Peek(9) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 173
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x183

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x938;
      assert s1.Peek(7) == 0x183;
      assert s1.Peek(8) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s174(s5, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 126
    * Starting at 0x938
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x183

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x183;
      assert s1.Peek(6) == 0x12b;
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
      assert s11.Peek(1) == 0x183;
      assert s11.Peek(4) == 0x12b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s13, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 37
    * Starting at 0x183
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x183 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push2(s1, 0x0369);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s3, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 69
    * Starting at 0x369
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x369 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Caller(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x02);
      var s8 := Push1(s7, 0x20);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x12b;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := Dup4(s13);
      var s15 := Keccak256(s14);
      var s16 := Push1(s15, 0x01);
      var s17 := Push1(s16, 0x01);
      var s18 := Push1(s17, 0xa0);
      var s19 := Shl(s18);
      var s20 := Sub(s19);
      var s21 := Dup8(s20);
      assert s21.Peek(9) == 0x12b;
      var s22 := And(s21);
      var s23 := Dup5(s22);
      var s24 := MStore(s23);
      var s25 := Swap1(s24);
      var s26 := Swap2(s25);
      var s27 := MStore(s26);
      var s28 := Dup2(s27);
      var s29 := Keccak256(s28);
      var s30 := SLoad(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(5) == 0x12b;
      var s32 := Swap2(s31);
      var s33 := Push2(s32, 0x02f7);
      var s34 := Swap2(s33);
      var s35 := Dup6(s34);
      var s36 := Swap1(s35);
      var s37 := Push2(s36, 0x035a);
      var s38 := Swap1(s37);
      var s39 := Dup7(s38);
      var s40 := Push2(s39, 0x0540);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s41, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 85
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x35a

    requires s0.stack[5] == 0x2f7

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x35a;
      assert s1.Peek(5) == 0x2f7;
      assert s1.Peek(9) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x054c);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0999);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s178(s7, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 133
    * Starting at 0x999
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x999 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x35a

    requires s0.stack[9] == 0x2f7

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x54c;
      assert s1.Peek(6) == 0x35a;
      assert s1.Peek(9) == 0x2f7;
      assert s1.Peek(13) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s180(s9, gas - 1)
      else
        ExecuteFromCFGNode_s179(s9, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 134
    * Starting at 0x9a5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x54c

    requires s0.stack[7] == 0x35a

    requires s0.stack[10] == 0x2f7

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x54c;
      assert s1.Peek(8) == 0x35a;
      assert s1.Peek(11) == 0x2f7;
      assert s1.Peek(15) == 0x12b;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Dup2(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 180
    * Segment Id for this node is: 135
    * Starting at 0x9b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x54c

    requires s0.stack[7] == 0x35a

    requires s0.stack[10] == 0x2f7

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x54c;
      assert s1.Peek(7) == 0x35a;
      assert s1.Peek(10) == 0x2f7;
      assert s1.Peek(14) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s5, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 86
    * Starting at 0x54c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x35a

    requires s0.stack[7] == 0x2f7

    requires s0.stack[11] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x35a;
      assert s1.Peek(7) == 0x2f7;
      assert s1.Peek(11) == 0x12b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s7, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 35
    * Starting at 0x160
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x05);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := Swap1(s6);
      var s8 := Swap2(s7);
      var s9 := And(s8);
      var s10 := Dup2(s9);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Push2(s13, 0x010f);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s15, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 33
    * Starting at 0x14d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x012b);
      var s3 := Push2(s2, 0x015b);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x08e2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s7, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 118
    * Starting at 0x8e2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x15b

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15b;
      assert s1.Peek(3) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x60);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x08f6);
      assert s11.Peek(0) == 0x8f6;
      assert s11.Peek(7) == 0x15b;
      assert s11.Peek(8) == 0x12b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s12, gas - 1)
      else
        ExecuteFromCFGNode_s185(s12, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 119
    * Starting at 0x8f3
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x15b

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(6) == 0x15b;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 186
    * Segment Id for this node is: 120
    * Starting at 0x8f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x15b

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x15b;
      assert s1.Peek(6) == 0x12b;
      var s2 := Push2(s1, 0x08ff);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s187(s5, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x8ff

    requires s0.stack[7] == 0x15b

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x8ff;
      assert s1.Peek(7) == 0x15b;
      assert s1.Peek(8) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x8ff;
      assert s11.Peek(10) == 0x15b;
      assert s11.Peek(11) == 0x12b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s14, gas - 1)
      else
        ExecuteFromCFGNode_s188(s14, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x8ff

    requires s0.stack[8] == 0x15b

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x8ff;
      assert s1.Peek(9) == 0x15b;
      assert s1.Peek(10) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 189
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x8ff

    requires s0.stack[8] == 0x15b

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x8ff;
      assert s1.Peek(8) == 0x15b;
      assert s1.Peek(9) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s5, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 121
    * Starting at 0x8ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x15b

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x15b;
      assert s1.Peek(7) == 0x12b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x090d);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup6(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x087a);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s191(s9, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x90d

    requires s0.stack[7] == 0x15b

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x90d;
      assert s1.Peek(7) == 0x15b;
      assert s1.Peek(8) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x90d;
      assert s11.Peek(10) == 0x15b;
      assert s11.Peek(11) == 0x12b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s193(s14, gas - 1)
      else
        ExecuteFromCFGNode_s192(s14, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x90d

    requires s0.stack[8] == 0x15b

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x90d;
      assert s1.Peek(9) == 0x15b;
      assert s1.Peek(10) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 193
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x90d

    requires s0.stack[8] == 0x15b

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x90d;
      assert s1.Peek(8) == 0x15b;
      assert s1.Peek(9) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s194(s5, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 122
    * Starting at 0x90d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x90d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x15b

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x15b;
      assert s1.Peek(7) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Swap3(s9);
      var s11 := Pop(s10);
      assert s11.Peek(4) == 0x15b;
      assert s11.Peek(5) == 0x12b;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Swap3(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s15, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 34
    * Starting at 0x15b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12b;
      var s2 := Push2(s1, 0x0300);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s3, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 64
    * Starting at 0x300
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x300 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x030d);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0678);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s8, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 94
    * Starting at 0x678
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x678 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x30d

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x30d;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x06dc);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s200(s10, gas - 1)
      else
        ExecuteFromCFGNode_s198(s10, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 95
    * Starting at 0x687
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x687 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x30d

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x30d;
      assert s1.Peek(9) == 0x12b;
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
      assert s11.Peek(6) == 0x30d;
      assert s11.Peek(11) == 0x12b;
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
      assert s21.Peek(6) == 0x30d;
      assert s21.Peek(11) == 0x12b;
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
      assert s31.Peek(4) == 0x30d;
      assert s31.Peek(9) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s33, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x30d

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x30d;
      assert s1.Peek(9) == 0x12b;
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

  /** Node 200
    * Segment Id for this node is: 96
    * Starting at 0x6dc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x30d

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x30d;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x073e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s10, gas - 1)
      else
        ExecuteFromCFGNode_s201(s10, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 97
    * Starting at 0x6eb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6eb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x30d

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x30d;
      assert s1.Peek(9) == 0x12b;
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
      assert s11.Peek(6) == 0x30d;
      assert s11.Peek(11) == 0x12b;
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
      assert s21.Peek(6) == 0x30d;
      assert s21.Peek(11) == 0x12b;
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
      assert s31.Peek(4) == 0x30d;
      assert s31.Peek(9) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s33, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 98
    * Starting at 0x73e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x30d

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x30d;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push2(s1, 0x077b);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(3) == 0x77b;
      assert s11.Peek(7) == 0x30d;
      assert s11.Peek(12) == 0x12b;
      var s12 := Push1(s11, 0x26);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x09f9);
      var s18 := Push1(s17, 0x26);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(3) == 0x77b;
      assert s21.Peek(7) == 0x30d;
      assert s21.Peek(12) == 0x12b;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0xa0);
      var s24 := Shl(s23);
      var s25 := Sub(s24);
      var s26 := Dup7(s25);
      var s27 := And(s26);
      var s28 := Push1(s27, 0x00);
      var s29 := Swap1(s28);
      var s30 := Dup2(s29);
      var s31 := MStore(s30);
      assert s31.Peek(3) == 0x77b;
      assert s31.Peek(7) == 0x30d;
      assert s31.Peek(12) == 0x12b;
      var s32 := Push1(s31, 0x01);
      var s33 := Push1(s32, 0x20);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := Swap1(s35);
      var s37 := Keccak256(s36);
      var s38 := SLoad(s37);
      var s39 := Swap2(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x07fe);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s203(s41, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 99
    * Starting at 0x77a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x7fe

    requires s0.stack[4] == 0x77b

    requires s0.stack[8] == 0x30d

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s1, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 103
    * Starting at 0x7fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x77b

    requires s0.stack[7] == 0x30d

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x77b;
      assert s1.Peek(7) == 0x30d;
      assert s1.Peek(12) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0822);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s9, gas - 1)
      else
        ExecuteFromCFGNode_s205(s9, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 104
    * Starting at 0x80a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x77b

    requires s0.stack[9] == 0x30d

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x77b;
      assert s1.Peek(10) == 0x30d;
      assert s1.Peek(15) == 0x12b;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f5);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f5;
      assert s11.Peek(7) == 0x77b;
      assert s11.Peek(11) == 0x30d;
      assert s11.Peek(16) == 0x12b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0946);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s206(s14, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 127
    * Starting at 0x946
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x946 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x3f5

    requires s0.stack[7] == 0x77b

    requires s0.stack[11] == 0x30d

    requires s0.stack[16] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f5;
      assert s1.Peek(7) == 0x77b;
      assert s1.Peek(11) == 0x30d;
      assert s1.Peek(16) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x77b;
      assert s11.Peek(17) == 0x30d;
      assert s11.Peek(22) == 0x12b;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s207(s14, gas - 1)
  }

  /** Node 207
    * Segment Id for this node is: 128
    * Starting at 0x956
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x956 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x30d

    requires s0.stack[20] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x77b;
      assert s1.Peek(15) == 0x30d;
      assert s1.Peek(20) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0972);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s7, gas - 1)
      else
        ExecuteFromCFGNode_s208(s7, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 129
    * Starting at 0x95f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x30d

    requires s0.stack[20] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x77b;
      assert s1.Peek(16) == 0x30d;
      assert s1.Peek(21) == 0x12b;
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
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x77b;
      assert s11.Peek(17) == 0x30d;
      assert s11.Peek(22) == 0x12b;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0956);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s207(s16, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 130
    * Starting at 0x972
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x30d

    requires s0.stack[20] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x77b;
      assert s1.Peek(15) == 0x30d;
      assert s1.Peek(20) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0983);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s7, gas - 1)
      else
        ExecuteFromCFGNode_s210(s7, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 131
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x30d

    requires s0.stack[20] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x77b;
      assert s1.Peek(16) == 0x30d;
      assert s1.Peek(21) == 0x12b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s211(s7, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 132
    * Starting at 0x983
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x77b

    requires s0.stack[15] == 0x30d

    requires s0.stack[20] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x77b;
      assert s1.Peek(15) == 0x30d;
      assert s1.Peek(20) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x3f5;
      assert s11.Peek(9) == 0x77b;
      assert s11.Peek(13) == 0x30d;
      assert s11.Peek(18) == 0x12b;
      var s12 := Push1(s11, 0x40);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s19, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x77b

    requires s0.stack[9] == 0x30d

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x77b;
      assert s1.Peek(9) == 0x30d;
      assert s1.Peek(14) == 0x12b;
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

  /** Node 213
    * Segment Id for this node is: 105
    * Starting at 0x822
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x822 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x77b

    requires s0.stack[9] == 0x30d

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x77b;
      assert s1.Peek(9) == 0x30d;
      assert s1.Peek(14) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s8, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 100
    * Starting at 0x77b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x77b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x30d

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x30d;
      assert s1.Peek(9) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup6(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Swap1(s10);
      assert s11.Peek(7) == 0x30d;
      assert s11.Peek(12) == 0x12b;
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
      assert s21.Peek(8) == 0x30d;
      assert s21.Peek(13) == 0x12b;
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
      assert s31.Peek(4) == 0x30d;
      assert s31.Peek(9) == 0x12b;
      var s32 := Push2(s31, 0x07aa);
      var s33 := Swap1(s32);
      var s34 := Dup3(s33);
      var s35 := Push2(s34, 0x0540);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s36, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 85
    * Starting at 0x540
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x7aa

    requires s0.stack[6] == 0x30d

    requires s0.stack[11] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7aa;
      assert s1.Peek(6) == 0x30d;
      assert s1.Peek(11) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x054c);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x0999);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s7, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 133
    * Starting at 0x999
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x999 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x54c

    requires s0.stack[6] == 0x7aa

    requires s0.stack[10] == 0x30d

    requires s0.stack[15] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x54c;
      assert s1.Peek(6) == 0x7aa;
      assert s1.Peek(10) == 0x30d;
      assert s1.Peek(15) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Not(s3);
      var s5 := Dup3(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x09b8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s9, gas - 1)
      else
        ExecuteFromCFGNode_s217(s9, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 134
    * Starting at 0x9a5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x54c

    requires s0.stack[7] == 0x7aa

    requires s0.stack[11] == 0x30d

    requires s0.stack[16] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(4) == 0x54c;
      assert s1.Peek(8) == 0x7aa;
      assert s1.Peek(12) == 0x30d;
      assert s1.Peek(17) == 0x12b;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x11);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Dup2(s9);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 218
    * Segment Id for this node is: 135
    * Starting at 0x9b8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x54c

    requires s0.stack[7] == 0x7aa

    requires s0.stack[11] == 0x30d

    requires s0.stack[16] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x54c;
      assert s1.Peek(7) == 0x7aa;
      assert s1.Peek(11) == 0x30d;
      assert s1.Peek(16) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s5, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 86
    * Starting at 0x54c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x7aa

    requires s0.stack[8] == 0x30d

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7aa;
      assert s1.Peek(8) == 0x30d;
      assert s1.Peek(13) == 0x12b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s220(s7, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 101
    * Starting at 0x7aa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x30d

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x30d;
      assert s1.Peek(9) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup1(s6);
      var s8 := Dup5(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(8) == 0x30d;
      assert s11.Peek(13) == 0x12b;
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
      assert s21.Peek(8) == 0x30d;
      assert s21.Peek(13) == 0x12b;
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
      assert s31.Peek(6) == 0x30d;
      assert s31.Peek(11) == 0x12b;
      var s32 := Push32(s31, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef);
      var s33 := Swap1(s32);
      var s34 := Push2(s33, 0x066b);
      var s35 := Swap1(s34);
      var s36 := Dup6(s35);
      var s37 := Dup2(s36);
      var s38 := MStore(s37);
      var s39 := Push1(s38, 0x20);
      var s40 := Add(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s221(s41, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 102
    * Starting at 0x7fd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x66b

    requires s0.stack[8] == 0x30d

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Jump(s0);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s1, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 93
    * Starting at 0x66b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x30d

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x30d;
      assert s1.Peek(12) == 0x12b;
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
      assert s11.Peek(0) == 0x30d;
      assert s11.Peek(5) == 0x12b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s12, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 65
    * Starting at 0x30d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x12b;
      var s2 := Push2(s1, 0x035f);
      var s3 := Dup5(s2);
      var s4 := Caller(s3);
      var s5 := Push2(s4, 0x035a);
      var s6 := Dup6(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x60);
      var s11 := Add(s10);
      assert s11.Peek(3) == 0x35a;
      assert s11.Peek(6) == 0x35f;
      assert s11.Peek(11) == 0x12b;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := Push1(s14, 0x28);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := Push2(s19, 0x0a1f);
      var s21 := Push1(s20, 0x28);
      assert s21.Peek(5) == 0x35a;
      assert s21.Peek(8) == 0x35f;
      assert s21.Peek(13) == 0x12b;
      var s22 := Swap2(s21);
      var s23 := CodeCopy(s22);
      var s24 := Push1(s23, 0x01);
      var s25 := Push1(s24, 0x01);
      var s26 := Push1(s25, 0xa0);
      var s27 := Shl(s26);
      var s28 := Sub(s27);
      var s29 := Dup11(s28);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x00);
      assert s31.Peek(4) == 0x35a;
      assert s31.Peek(7) == 0x35f;
      assert s31.Peek(12) == 0x12b;
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
      ExecuteFromCFGNode_s224(s41, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 66
    * Starting at 0x349
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x349 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x35a

    requires s0.stack[9] == 0x35f

    requires s0.stack[14] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x35a;
      assert s1.Peek(10) == 0x35f;
      assert s1.Peek(15) == 0x12b;
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
      assert s11.Peek(3) == 0x35a;
      assert s11.Peek(6) == 0x35f;
      assert s11.Peek(11) == 0x12b;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x07fe);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s15, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 103
    * Starting at 0x7fe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7fe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x35a

    requires s0.stack[6] == 0x35f

    requires s0.stack[11] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35a;
      assert s1.Peek(6) == 0x35f;
      assert s1.Peek(11) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Dup5(s3);
      var s5 := Dup5(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0822);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s234(s9, gas - 1)
      else
        ExecuteFromCFGNode_s226(s9, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 104
    * Starting at 0x80a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x35a

    requires s0.stack[8] == 0x35f

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x35a;
      assert s1.Peek(9) == 0x35f;
      assert s1.Peek(14) == 0x12b;
      var s2 := MLoad(s1);
      var s3 := Push3(s2, 0x461bcd);
      var s4 := Push1(s3, 0xe5);
      var s5 := Shl(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x04);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x03f5);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x3f5;
      assert s11.Peek(7) == 0x35a;
      assert s11.Peek(10) == 0x35f;
      assert s11.Peek(15) == 0x12b;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x0946);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s14, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 127
    * Starting at 0x946
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x946 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x3f5

    requires s0.stack[7] == 0x35a

    requires s0.stack[10] == 0x35f

    requires s0.stack[15] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3f5;
      assert s1.Peek(7) == 0x35a;
      assert s1.Peek(10) == 0x35f;
      assert s1.Peek(15) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := MStore(s5);
      var s7 := Dup4(s6);
      var s8 := MLoad(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x35a;
      assert s11.Peek(16) == 0x35f;
      assert s11.Peek(21) == 0x12b;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Dup3(s13);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s228(s14, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 128
    * Starting at 0x956
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x956 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x35f

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(14) == 0x35f;
      assert s1.Peek(19) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0972);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s7, gas - 1)
      else
        ExecuteFromCFGNode_s229(s7, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 129
    * Starting at 0x95f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x35f

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup6(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x35a;
      assert s1.Peek(15) == 0x35f;
      assert s1.Peek(20) == 0x12b;
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
      assert s11.Peek(8) == 0x3f5;
      assert s11.Peek(13) == 0x35a;
      assert s11.Peek(16) == 0x35f;
      assert s11.Peek(21) == 0x12b;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x0956);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s16, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 130
    * Starting at 0x972
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x972 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x35f

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(14) == 0x35f;
      assert s1.Peek(19) == 0x12b;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0983);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s232(s7, gas - 1)
      else
        ExecuteFromCFGNode_s231(s7, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 131
    * Starting at 0x97b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x35f

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(7) == 0x3f5;
      assert s1.Peek(12) == 0x35a;
      assert s1.Peek(15) == 0x35f;
      assert s1.Peek(20) == 0x12b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s232(s7, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 132
    * Starting at 0x983
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x983 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[6] == 0x3f5

    requires s0.stack[11] == 0x35a

    requires s0.stack[14] == 0x35f

    requires s0.stack[19] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3f5;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(14) == 0x35f;
      assert s1.Peek(19) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x1f);
      var s4 := Add(s3);
      var s5 := Push1(s4, 0x1f);
      var s6 := Not(s5);
      var s7 := And(s6);
      var s8 := Swap3(s7);
      var s9 := Swap1(s8);
      var s10 := Swap3(s9);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x3f5;
      assert s11.Peek(9) == 0x35a;
      assert s11.Peek(12) == 0x35f;
      assert s11.Peek(17) == 0x12b;
      var s12 := Push1(s11, 0x40);
      var s13 := Add(s12);
      var s14 := Swap4(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s19, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x35a

    requires s0.stack[8] == 0x35f

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x35a;
      assert s1.Peek(8) == 0x35f;
      assert s1.Peek(13) == 0x12b;
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

  /** Node 234
    * Segment Id for this node is: 105
    * Starting at 0x822
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x822 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[5] == 0x35a

    requires s0.stack[8] == 0x35f

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x35a;
      assert s1.Peek(8) == 0x35f;
      assert s1.Peek(13) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap1(s4);
      var s6 := Sub(s5);
      var s7 := Swap1(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s8, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 67
    * Starting at 0x35a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x35f

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35f;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push2(s1, 0x0553);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s3, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 87
    * Starting at 0x553
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x553 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x35f

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35f;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x05b5);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s10, gas - 1)
      else
        ExecuteFromCFGNode_s237(s10, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 88
    * Starting at 0x562
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x562 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x35f

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x35f;
      assert s1.Peek(9) == 0x12b;
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
      assert s11.Peek(6) == 0x35f;
      assert s11.Peek(11) == 0x12b;
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
      assert s21.Peek(6) == 0x35f;
      assert s21.Peek(11) == 0x12b;
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
      assert s31.Peek(4) == 0x35f;
      assert s31.Peek(9) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s33, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 72
    * Starting at 0x3f5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x35f

    requires s0.stack[9] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x35f;
      assert s1.Peek(9) == 0x12b;
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

  /** Node 239
    * Segment Id for this node is: 89
    * Starting at 0x5b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x35f

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35f;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup3(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0616);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s241(s10, gas - 1)
      else
        ExecuteFromCFGNode_s240(s10, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 90
    * Starting at 0x5c4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x35f

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x35f;
      assert s1.Peek(9) == 0x12b;
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
      assert s11.Peek(6) == 0x35f;
      assert s11.Peek(11) == 0x12b;
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
      assert s21.Peek(6) == 0x35f;
      assert s21.Peek(11) == 0x12b;
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
      assert s31.Peek(4) == 0x35f;
      assert s31.Peek(9) == 0x12b;
      var s32 := Push2(s31, 0x03f5);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s33, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 91
    * Starting at 0x616
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x616 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x35f

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35f;
      assert s1.Peek(8) == 0x12b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup4(s6);
      var s8 := Dup2(s7);
      var s9 := And(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x35f;
      assert s11.Peek(12) == 0x12b;
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
      assert s21.Peek(10) == 0x35f;
      assert s21.Peek(15) == 0x12b;
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
      assert s31.Peek(8) == 0x35f;
      assert s31.Peek(13) == 0x12b;
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
      ExecuteFromCFGNode_s242(s41, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 92
    * Starting at 0x646
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x646 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x35f

    requires s0.stack[13] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(9) == 0x35f;
      assert s1.Peek(14) == 0x12b;
      var s2 := MStore(s1);
      var s3 := Push32(s2, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s243(s5, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 93
    * Starting at 0x66b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x66b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[7] == 0x35f

    requires s0.stack[12] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x35f;
      assert s1.Peek(12) == 0x12b;
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
      assert s11.Peek(0) == 0x35f;
      assert s11.Peek(5) == 0x12b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s12, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 68
    * Starting at 0x35f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x12b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s9, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 21
    * Starting at 0xd3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
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
      var s5 := Push2(s4, 0x00fa);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s6, gas - 1)
      else
        ExecuteFromCFGNode_s246(s6, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 22
    * Starting at 0xdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x095ea7b3);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0118);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s5, gas - 1)
      else
        ExecuteFromCFGNode_s247(s5, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x18160ddd);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x013b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s249(s5, gas - 1)
      else
        ExecuteFromCFGNode_s248(s5, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 24
    * Starting at 0xf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
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

  /** Node 249
    * Segment Id for this node is: 31
    * Starting at 0x13b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x06);
      var s3 := SLoad(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s44(s3, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 28
    * Starting at 0x118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x012b);
      var s3 := Push2(s2, 0x0126);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x091d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s7, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 123
    * Starting at 0x91d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x126

    requires s0.stack[3] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x126;
      assert s1.Peek(3) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x092f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s253(s11, gas - 1)
      else
        ExecuteFromCFGNode_s252(s11, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 124
    * Starting at 0x92c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x126

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x126;
      assert s1.Peek(6) == 0x12b;
      var s2 := Dup3(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 253
    * Segment Id for this node is: 125
    * Starting at 0x92f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x92f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x126

    requires s0.stack[5] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x126;
      assert s1.Peek(5) == 0x12b;
      var s2 := Push2(s1, 0x0938);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x087a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s5, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 107
    * Starting at 0x87a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x87a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x938

    requires s0.stack[6] == 0x126

    requires s0.stack[7] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x938;
      assert s1.Peek(6) == 0x126;
      assert s1.Peek(7) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x938;
      assert s11.Peek(9) == 0x126;
      assert s11.Peek(10) == 0x12b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x0891);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s256(s14, gas - 1)
      else
        ExecuteFromCFGNode_s255(s14, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 108
    * Starting at 0x88d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x126

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x938;
      assert s1.Peek(8) == 0x126;
      assert s1.Peek(9) == 0x12b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 256
    * Segment Id for this node is: 109
    * Starting at 0x891
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x891 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x938

    requires s0.stack[7] == 0x126

    requires s0.stack[8] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x938;
      assert s1.Peek(7) == 0x126;
      assert s1.Peek(8) == 0x12b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s5, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 126
    * Starting at 0x938
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x938 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x126

    requires s0.stack[6] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x126;
      assert s1.Peek(6) == 0x12b;
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
      assert s11.Peek(1) == 0x126;
      assert s11.Peek(4) == 0x12b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s258(s13, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 29
    * Starting at 0x126
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x126 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push2(s1, 0x02ea);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s3, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 62
    * Starting at 0x2ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x12b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x12b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02f7);
      var s4 := Caller(s3);
      var s5 := Dup5(s4);
      var s6 := Dup5(s5);
      var s7 := Push2(s6, 0x0553);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s8, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 25
    * Starting at 0xfa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0102);
      var s3 := Push2(s2, 0x0258);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s4, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 53
    * Starting at 0x258
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x258 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x102

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x102;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x03);
      var s4 := Dup1(s3);
      var s5 := SLoad(s4);
      var s6 := Push2(s5, 0x0267);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x09bd);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s9, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 24
    * Starting at 0xf5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
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