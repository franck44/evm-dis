include "../../../../src/dafny/AbstractSemantics/AbstractSemantics.dfy"

module  {:disableNonlinearArithmetic} EVMProofObject {

  import opened AbstractSemantics
  import opened AbstractState

  /** Node 0
    * Segment Id for this node is: 0
    * Starting at 0x0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
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
      var s4 := Push1(s3, 0x0a);
      var s5 := Push1(s4, 0x0c);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s1(s6, gas - 1)
  }

  /** Node 1
    * Segment Id for this node is: 2
    * Starting at 0xc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s1(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xa;
      var s2 := Push1(s1, 0x18);
      var s3 := Push1(s2, 0x14);
      var s4 := Push1(s3, 0x1a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s2(s5, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 5
    * Starting at 0x1a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s2(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x14

    requires s0.stack[1] == 0x18

    requires s0.stack[2] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x14;
      assert s1.Peek(1) == 0x18;
      assert s1.Peek(2) == 0xa;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x00000000000000000000000061f4464a654fe799b78b41413ea2a20acebc70ab);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := And(s8);
      var s10 := Push4(s9, 0x5c60da1b);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(4) == 0x14;
      assert s11.Peek(5) == 0x18;
      assert s11.Peek(6) == 0xa;
      var s12 := MLoad(s11);
      var s13 := Dup2(s12);
      var s14 := Push4(s13, 0xffffffff);
      var s15 := And(s14);
      var s16 := Push1(s15, 0xe0);
      var s17 := Shl(s16);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x04);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x14;
      assert s21.Peek(5) == 0x18;
      assert s21.Peek(6) == 0xa;
      var s22 := Push1(s21, 0x20);
      var s23 := Push1(s22, 0x40);
      var s24 := MLoad(s23);
      var s25 := Dup1(s24);
      var s26 := Dup4(s25);
      var s27 := Sub(s26);
      var s28 := Dup2(s27);
      var s29 := Dup7(s28);
      var s30 := Gas(s29);
      var s31 := StaticCall(s30);
      assert s31.Peek(5) == 0x14;
      assert s31.Peek(6) == 0x18;
      assert s31.Peek(7) == 0xa;
      var s32 := IsZero(s31);
      var s33 := Dup1(s32);
      var s34 := IsZero(s33);
      var s35 := Push1(s34, 0x79);
      var s36 := JumpI(s35);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s35.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s36, gas - 1)
      else
        ExecuteFromCFGNode_s3(s36, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 6
    * Starting at 0x70
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s3(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x14

    requires s0.stack[6] == 0x18

    requires s0.stack[7] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(6) == 0x14;
      assert s1.Peek(7) == 0x18;
      assert s1.Peek(8) == 0xa;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 4
    * Segment Id for this node is: 7
    * Starting at 0x79
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x14

    requires s0.stack[6] == 0x18

    requires s0.stack[7] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14;
      assert s1.Peek(6) == 0x18;
      assert s1.Peek(7) == 0xa;
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
      assert s11.Peek(5) == 0x14;
      assert s11.Peek(6) == 0x18;
      assert s11.Peek(7) == 0xa;
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
      assert s21.Peek(4) == 0x14;
      assert s21.Peek(5) == 0x18;
      assert s21.Peek(6) == 0xa;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push1(s23, 0x9b);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push1(s26, 0xc3);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s5(s28, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 12
    * Starting at 0xc3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x9b

    requires s0.stack[4] == 0x14

    requires s0.stack[5] == 0x18

    requires s0.stack[6] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x9b;
      assert s1.Peek(4) == 0x14;
      assert s1.Peek(5) == 0x18;
      assert s1.Peek(6) == 0xa;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push1(s8, 0xd4);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s10, gas - 1)
      else
        ExecuteFromCFGNode_s6(s10, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 13
    * Starting at 0xd0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x9b

    requires s0.stack[5] == 0x14

    requires s0.stack[6] == 0x18

    requires s0.stack[7] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x9b;
      assert s1.Peek(6) == 0x14;
      assert s1.Peek(7) == 0x18;
      assert s1.Peek(8) == 0xa;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 7
    * Segment Id for this node is: 14
    * Starting at 0xd4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x9b

    requires s0.stack[5] == 0x14

    requires s0.stack[6] == 0x18

    requires s0.stack[7] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x9b;
      assert s1.Peek(5) == 0x14;
      assert s1.Peek(6) == 0x18;
      assert s1.Peek(7) == 0xa;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x9b;
      assert s11.Peek(8) == 0x14;
      assert s11.Peek(9) == 0x18;
      assert s11.Peek(10) == 0xa;
      var s12 := Eq(s11);
      var s13 := Push1(s12, 0xea);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s9(s14, gas - 1)
      else
        ExecuteFromCFGNode_s8(s14, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 15
    * Starting at 0xe6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9b

    requires s0.stack[6] == 0x14

    requires s0.stack[7] == 0x18

    requires s0.stack[8] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x9b;
      assert s1.Peek(7) == 0x14;
      assert s1.Peek(8) == 0x18;
      assert s1.Peek(9) == 0xa;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 9
    * Segment Id for this node is: 16
    * Starting at 0xea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9b

    requires s0.stack[6] == 0x14

    requires s0.stack[7] == 0x18

    requires s0.stack[8] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9b;
      assert s1.Peek(6) == 0x14;
      assert s1.Peek(7) == 0x18;
      assert s1.Peek(8) == 0xa;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s7, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 8
    * Starting at 0x9b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x14

    requires s0.stack[3] == 0x18

    requires s0.stack[4] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14;
      assert s1.Peek(3) == 0x18;
      assert s1.Peek(4) == 0xa;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s5, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 3
    * Starting at 0x14
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18

    requires s0.stack[2] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18;
      assert s1.Peek(2) == 0xa;
      var s2 := Push1(s1, 0xa0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s3, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 9
    * Starting at 0xa0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18

    requires s0.stack[2] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18;
      assert s1.Peek(2) == 0xa;
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
      assert s11.Peek(7) == 0x18;
      assert s11.Peek(8) == 0xa;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push1(s19, 0xbe);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s14(s21, gas - 1)
      else
        ExecuteFromCFGNode_s13(s21, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 10
    * Starting at 0xba
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x18

    requires s0.stack[4] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x18;
      assert s1.Peek(5) == 0xa;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 14
    * Segment Id for this node is: 11
    * Starting at 0xbe
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x18

    requires s0.stack[4] == 0xa

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x18;
      assert s1.Peek(4) == 0xa;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }
}
