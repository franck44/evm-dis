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
      var s1 := Push1(s0, 0x03);
      var s2 := CallDataSize(s1);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x000c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s3(s5, gas - 1)
      else
        ExecuteFromCFGNode_s1(s5, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 1
    * Starting at 0x8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x048c);
      assert s1.Peek(0) == 0x48c;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s2, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 74
    * Starting at 0x48c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 3
    * Segment Id for this node is: 2
    * Starting at 0xc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0xe0);
      var s5 := Shr(s4);
      var s6 := CallValue(s5);
      var s7 := Push2(s6, 0x0492);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s8, gas - 1)
      else
        ExecuteFromCFGNode_s4(s8, gas - 1)
  }

  /** Node 4
    * Segment Id for this node is: 3
    * Starting at 0x18
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x87121759);
      var s2 := Dup2(s1);
      var s3 := Xor(s2);
      var s4 := Push2(s3, 0x0034);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s34(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 4
    * Starting at 0x23
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x64);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 5
    * Starting at 0x2b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Push1(s1, 0x80);
      var s3 := MStore(s2);
      var s4 := Push2(s3, 0x004e);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s5, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 9
    * Starting at 0x4e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x04);
      var s3 := CallDataLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shr(s5);
      var s7 := Push2(s6, 0x0492);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s8, gas - 1)
      else
        ExecuteFromCFGNode_s8(s8, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 10
    * Starting at 0x5a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shr(s6);
      var s8 := Push2(s7, 0x0492);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s9, gas - 1)
      else
        ExecuteFromCFGNode_s9(s9, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 11
    * Starting at 0x68
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x60);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x44);
      var s4 := CallDataLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0xa0);
      var s8 := MLoad(s7);
      var s9 := Not(s8);
      var s10 := Push2(s9, 0x00b2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s11, gas - 1)
      else
        ExecuteFromCFGNode_s10(s11, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 12
    * Starting at 0x79
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x70a08231);
      var s4 := Push1(s3, 0xc0);
      var s5 := MStore(s4);
      var s6 := Caller(s5);
      var s7 := Push1(s6, 0xe0);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push1(s9, 0xc0);
      var s11 := Push1(s10, 0x24);
      var s12 := Push1(s11, 0xdc);
      var s13 := Dup5(s12);
      var s14 := Gas(s13);
      var s15 := StaticCall(s14);
      var s16 := Push2(s15, 0x00a1);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s17, gas - 1)
      else
        ExecuteFromCFGNode_s11(s17, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 13
    * Starting at 0x97
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x97 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 12
    * Segment Id for this node is: 14
    * Starting at 0xa1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := ReturnDataSize(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0492);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s6, gas - 1)
      else
        ExecuteFromCFGNode_s13(s6, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 15
    * Starting at 0xaa
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0xc0);
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xa0);
      var s6 := MStore(s5);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s14(s6, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 16
    * Starting at 0xb2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x80);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := MLoad(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0492);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s8, gas - 1)
      else
        ExecuteFromCFGNode_s15(s8, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 17
    * Starting at 0xbe
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push4(s2, 0x23b872dd);
      var s4 := Push1(s3, 0xc0);
      var s5 := MStore(s4);
      var s6 := Caller(s5);
      var s7 := Push1(s6, 0xe0);
      var s8 := MStore(s7);
      var s9 := Address(s8);
      var s10 := Push2(s9, 0x0100);
      var s11 := MStore(s10);
      var s12 := Push1(s11, 0xa0);
      var s13 := MLoad(s12);
      var s14 := Push2(s13, 0x0120);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Push1(s16, 0xc0);
      var s18 := Push1(s17, 0x64);
      var s19 := Push1(s18, 0xdc);
      var s20 := Push1(s19, 0x00);
      var s21 := Dup6(s20);
      var s22 := Gas(s21);
      var s23 := Call(s22);
      var s24 := Push2(s23, 0x00f4);
      var s25 := JumpI(s24);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s24.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s25, gas - 1)
      else
        ExecuteFromCFGNode_s16(s25, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 18
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 17
    * Segment Id for this node is: 19
    * Starting at 0xf4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := ReturnDataSize(s1);
      var s3 := Push2(s2, 0x010b);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s30(s4, gas - 1)
      else
        ExecuteFromCFGNode_s18(s4, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 20
    * Starting at 0xfa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := ExtCodeSize(s1);
      var s3 := IsZero(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s5, gas - 1)
      else
        ExecuteFromCFGNode_s19(s5, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 21
    * Starting at 0x101
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x101 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := Push2(s1, 0x0140);
      var s3 := MStore(s2);
      var s4 := Push2(s3, 0x0123);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s5, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 25
    * Starting at 0x123
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0140);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := MLoad(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0492);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s8, gas - 1)
      else
        ExecuteFromCFGNode_s21(s8, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 26
    * Starting at 0x12f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Push2(s1, 0x04c4);
      var s3 := Push1(s2, 0x00);
      var s4 := CodeCopy(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0xc0);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Push2(s9, 0x04a4);
      var s11 := Push1(s10, 0x00);
      var s12 := CodeCopy(s11);
      var s13 := Push1(s12, 0x00);
      var s14 := MLoad(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Eq(s16);
      var s18 := Push2(s17, 0x016c);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s23(s19, gas - 1)
      else
        ExecuteFromCFGNode_s22(s19, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 27
    * Starting at 0x150
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x150 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Push1(s8, 0x00);
      var s10 := Keccak256(s9);
      var s11 := SLoad(s10);
      var s12 := Push1(s11, 0xc0);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0xc0);
      var s15 := MLoad(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0492);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s18, gas - 1)
      else
        ExecuteFromCFGNode_s23(s18, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 28
    * Starting at 0x16c
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x838b2520);
      var s3 := Push2(s2, 0x0104);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push1(s5, 0xc0);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push2(s8, 0x0124);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0xc0);
      var s12 := MLoad(s11);
      var s13 := Push2(s12, 0x0144);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x60);
      var s16 := MLoad(s15);
      var s17 := Push2(s16, 0x0164);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0xa0);
      var s20 := MLoad(s19);
      var s21 := Push2(s20, 0x0184);
      var s22 := MStore(s21);
      var s23 := Push3(s22, 0x030d40);
      var s24 := Push2(s23, 0x01a4);
      var s25 := MStore(s24);
      var s26 := Dup1(s25);
      var s27 := Push2(s26, 0x01c4);
      var s28 := MStore(s27);
      var s29 := Push1(s28, 0x00);
      var s30 := Push1(s29, 0xe0);
      var s31 := MStore(s30);
      var s32 := Push1(s31, 0xe0);
      var s33 := Dup2(s32);
      var s34 := Push2(s33, 0x0124);
      var s35 := Add(s34);
      var s36 := Dup2(s35);
      var s37 := MLoad(s36);
      var s38 := Dup1(s37);
      var s39 := Dup3(s38);
      var s40 := MStore(s39);
      var s41 := Pop(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s24(s41, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 29
    * Starting at 0x1b5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Dup3(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Sub(s10);
      var s12 := And(s11);
      var s13 := CallDataSize(s12);
      var s14 := Dup3(s13);
      var s15 := CallDataCopy(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Push1(s17, 0x1f);
      var s19 := Not(s18);
      var s20 := Push1(s19, 0x1f);
      var s21 := Dup3(s20);
      var s22 := MLoad(s21);
      var s23 := Push1(s22, 0x20);
      var s24 := Add(s23);
      var s25 := Add(s24);
      var s26 := And(s25);
      var s27 := Swap1(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Dup2(s30);
      var s32 := Add(s31);
      var s33 := Swap1(s32);
      var s34 := Pop(s33);
      var s35 := Add(s34);
      var s36 := Push2(s35, 0x0100);
      var s37 := MStore(s36);
      var s38 := Push2(s37, 0x0100);
      var s39 := Pop(s38);
      var s40 := Push1(s39, 0x00);
      var s41 := Push1(s40, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s25(s41, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 30
    * Starting at 0x1ea
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x0120);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x20);
      var s6 := Push2(s5, 0x04e4);
      var s7 := Push1(s6, 0x00);
      var s8 := CodeCopy(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := MLoad(s9);
      var s11 := Gas(s10);
      var s12 := Call(s11);
      var s13 := Push2(s12, 0x020e);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s14, gas - 1)
      else
        ExecuteFromCFGNode_s26(s14, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 31
    * Starting at 0x204
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x204 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 27
    * Segment Id for this node is: 32
    * Starting at 0x20e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20e as nat
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

  /** Node 28
    * Segment Id for this node is: 75
    * Starting at 0x492
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
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

  /** Node 29
    * Segment Id for this node is: 75
    * Starting at 0x492
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

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

  /** Node 30
    * Segment Id for this node is: 22
    * Starting at 0x10b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := ReturnDataSize(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0492);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s6, gas - 1)
      else
        ExecuteFromCFGNode_s31(s6, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 23
    * Starting at 0x114
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0xc0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Shr(s4);
      var s6 := Push2(s5, 0x0492);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s7, gas - 1)
      else
        ExecuteFromCFGNode_s32(s7, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 24
    * Starting at 0x11f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0140);
      var s2 := MStore(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s20(s2, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 75
    * Starting at 0x492
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

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

  /** Node 34
    * Segment Id for this node is: 6
    * Starting at 0x34
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0xe5361522);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x0210);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s6, gas - 1)
      else
        ExecuteFromCFGNode_s35(s6, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 7
    * Starting at 0x40
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x84);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s36(s5, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 8
    * Starting at 0x48
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x64);
      var s2 := CallDataLoad(s1);
      var s3 := Push1(s2, 0x80);
      var s4 := MStore(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s7(s4, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 33
    * Starting at 0x210
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0xc23697a8);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x023c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s6, gas - 1)
      else
        ExecuteFromCFGNode_s38(s6, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 34
    * Starting at 0x21c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x24);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s39(s5, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 35
    * Starting at 0x224
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x224 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shr(s4);
      var s6 := Push2(s5, 0x0492);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s7, gas - 1)
      else
        ExecuteFromCFGNode_s40(s7, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 36
    * Starting at 0x22f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x60);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x60);
      var s8 := Return(s7);
      // Segment is terminal (Revert, Stop or Return)
      s8
  }

  /** Node 41
    * Segment Id for this node is: 37
    * Starting at 0x23c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x13faede6);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x025a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s44(s6, gas - 1)
      else
        ExecuteFromCFGNode_s42(s6, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 38
    * Starting at 0x248
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x248 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s43(s5, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 39
    * Starting at 0x250
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x250 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Push1(s4, 0x40);
      var s6 := Return(s5);
      // Segment is terminal (Revert, Stop or Return)
      s6
  }

  /** Node 44
    * Segment Id for this node is: 40
    * Starting at 0x25a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x54808c61);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x038d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s6, gas - 1)
      else
        ExecuteFromCFGNode_s45(s6, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 41
    * Starting at 0x266
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x266 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x44);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s46(s5, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 42
    * Starting at 0x26e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shr(s4);
      var s6 := Push2(s5, 0x0492);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s7, gas - 1)
      else
        ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 43
    * Starting at 0x279
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x279 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x24);
      var s4 := CallDataLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shr(s6);
      var s8 := Push2(s7, 0x0492);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s9, gas - 1)
      else
        ExecuteFromCFGNode_s48(s9, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 44
    * Starting at 0x287
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x287 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x60);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Caller(s4);
      var s6 := Xor(s5);
      var s7 := Push2(s6, 0x0492);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s8, gas - 1)
      else
        ExecuteFromCFGNode_s49(s8, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 45
    * Starting at 0x293
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x293 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      var s2 := Push2(s1, 0x04a4);
      var s3 := Push1(s2, 0x00);
      var s4 := CodeCopy(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Eq(s8);
      var s10 := Push2(s9, 0x0492);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s11, gas - 1)
      else
        ExecuteFromCFGNode_s50(s11, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 46
    * Starting at 0x2a6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      var s2 := Push1(s1, 0x80);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := MLoad(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x02d7);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s8, gas - 1)
      else
        ExecuteFromCFGNode_s51(s8, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 47
    * Starting at 0x2b3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s2 := Push1(s1, 0x80);
      var s3 := MStore(s2);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 48
    * Starting at 0x2d7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push4(s3, 0x095ea7b3);
      var s5 := Push1(s4, 0xa0);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push2(s7, 0x04e4);
      var s9 := Push1(s8, 0x00);
      var s10 := CodeCopy(s9);
      var s11 := Push1(s10, 0x00);
      var s12 := MLoad(s11);
      var s13 := Push1(s12, 0xc0);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x80);
      var s16 := MLoad(s15);
      var s17 := Push1(s16, 0xe0);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Push1(s19, 0xa0);
      var s21 := Push1(s20, 0x44);
      var s22 := Push1(s21, 0xbc);
      var s23 := Push1(s22, 0x00);
      var s24 := Dup6(s23);
      var s25 := Gas(s24);
      var s26 := Call(s25);
      var s27 := Push2(s26, 0x0312);
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s28, gas - 1)
      else
        ExecuteFromCFGNode_s53(s28, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 49
    * Starting at 0x308
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x00);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 54
    * Segment Id for this node is: 50
    * Starting at 0x312
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x312 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x20);
      var s3 := ReturnDataSize(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0492);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s6, gas - 1)
      else
        ExecuteFromCFGNode_s55(s6, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 51
    * Starting at 0x31b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0xa0);
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Shr(s4);
      var s6 := Push2(s5, 0x0492);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s7, gas - 1)
      else
        ExecuteFromCFGNode_s56(s7, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 52
    * Starting at 0x326
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x326 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0100);
      var s2 := MStore(s1);
      var s3 := Push2(s2, 0x0100);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := MLoad(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0492);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s9, gas - 1)
      else
        ExecuteFromCFGNode_s57(s9, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 53
    * Starting at 0x335
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x335 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x2069a26c43c36ffaabe0c2d19bf65e55dd03abecdc449f5cc9663491e97f709d);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x40);
      var s12 := Push1(s11, 0x00);
      var s13 := Keccak256(s12);
      var s14 := SLoad(s13);
      var s15 := Push1(s14, 0xa0);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x60);
      var s18 := MLoad(s17);
      var s19 := Push1(s18, 0xc0);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x40);
      var s22 := Push1(s21, 0xa0);
      var s23 := Log2(s22);
      var s24 := Push1(s23, 0x60);
      var s25 := MLoad(s24);
      var s26 := Push1(s25, 0x00);
      var s27 := Push1(s26, 0x40);
      var s28 := MLoad(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x00);
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x40);
      var s34 := Push1(s33, 0x00);
      var s35 := Keccak256(s34);
      var s36 := SStore(s35);
      var s37 := Stop(s36);
      // Segment is terminal (Revert, Stop or Return)
      s37
  }

  /** Node 58
    * Segment Id for this node is: 54
    * Starting at 0x38d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x6b441a40);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x03bf);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s6, gas - 1)
      else
        ExecuteFromCFGNode_s59(s6, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 55
    * Starting at 0x399
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x399 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x24);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 56
    * Starting at 0x3a1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shr(s4);
      var s6 := Push2(s5, 0x0492);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s7, gas - 1)
      else
        ExecuteFromCFGNode_s61(s7, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 57
    * Starting at 0x3ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Caller(s4);
      var s6 := Xor(s5);
      var s7 := Push2(s6, 0x0492);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s8, gas - 1)
      else
        ExecuteFromCFGNode_s62(s8, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 58
    * Starting at 0x3b8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MLoad(s1);
      var s3 := Push1(s2, 0x02);
      var s4 := SStore(s3);
      var s5 := Stop(s4);
      // Segment is terminal (Revert, Stop or Return)
      s5
  }

  /** Node 63
    * Segment Id for this node is: 59
    * Starting at 0x3bf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0xe5ea47b8);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x0411);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s6, gas - 1)
      else
        ExecuteFromCFGNode_s64(s6, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 60
    * Starting at 0x3cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s65(s5, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 61
    * Starting at 0x3d3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      var s2 := SLoad(s1);
      var s3 := Caller(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x0492);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s6, gas - 1)
      else
        ExecuteFromCFGNode_s66(s6, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 62
    * Starting at 0x3dc
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x5c486528ec3e3f0ea91181cff8116f02bfa350e03b8b6f12e00765adbb5af85c);
      var s2 := Push1(s1, 0x01);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MStore(s4);
      var s6 := Caller(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := Push1(s9, 0x40);
      var s11 := Log1(s10);
      var s12 := Caller(s11);
      var s13 := Push1(s12, 0x01);
      var s14 := SStore(s13);
      var s15 := Stop(s14);
      // Segment is terminal (Revert, Stop or Return)
      s15
  }

  /** Node 67
    * Segment Id for this node is: 63
    * Starting at 0x411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x23f40db4);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x044c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s6, gas - 1)
      else
        ExecuteFromCFGNode_s68(s6, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 64
    * Starting at 0x41d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x24);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s69(s5, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 65
    * Starting at 0x425
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x425 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shr(s4);
      var s6 := Push2(s5, 0x0492);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s7, gas - 1)
      else
        ExecuteFromCFGNode_s70(s7, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 66
    * Starting at 0x430
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x430 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      var s2 := MStore(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x00);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := Push1(s10, 0x00);
      var s12 := Keccak256(s11);
      var s13 := SLoad(s12);
      var s14 := Push1(s13, 0x60);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Push1(s16, 0x60);
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 71
    * Segment Id for this node is: 67
    * Starting at 0x44c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x8da5cb5b);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x046b);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s6, gas - 1)
      else
        ExecuteFromCFGNode_s72(s6, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 68
    * Starting at 0x458
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x458 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s73(s5, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 69
    * Starting at 0x460
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x460 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push1(s5, 0x40);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 74
    * Segment Id for this node is: 70
    * Starting at 0x46b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push4(s1, 0x1ec0cdc1);
      var s3 := Dup2(s2);
      var s4 := Xor(s3);
      var s5 := Push2(s4, 0x048a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s6, gas - 1)
      else
        ExecuteFromCFGNode_s75(s6, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 71
    * Starting at 0x477
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x477 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x04);
      var s2 := CallDataSize(s1);
      var s3 := Lt(s2);
      var s4 := Push2(s3, 0x0492);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s5, gas - 1)
      else
        ExecuteFromCFGNode_s76(s5, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 72
    * Starting at 0x47f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x47f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x02);
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Push1(s5, 0x40);
      var s7 := Return(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 77
    * Segment Id for this node is: 73
    * Starting at 0x48a
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48a as nat
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
