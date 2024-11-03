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
      var s6 := Push2(s5, 0x0177);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s474(s7, gas - 1)
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
      var s6 := Push4(s5, 0x97fa4f40);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x00d8);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s196(s9, gas - 1)
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
      var s2 := Push4(s1, 0xcecaef21);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x008c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s145(s5, gas - 1)
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
      var s2 := Push4(s1, 0xe2876713);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s5, gas - 1)
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
      var s2 := Push4(s1, 0xe2876713);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02af);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf3d4149c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02b7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s5, gas - 1)
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
      var s2 := Push4(s1, 0xfcdb60db);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02bf);
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
    * Segment Id for this node is: 71
    * Starting at 0x2bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01cc);
      var s3 := Push2(s2, 0x0fbc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s11(s4, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 139
    * Starting at 0xfbc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfbc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1cc;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e7375626d69742e62616c616e6365732e656e61626c656400);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0302);
      assert s21.Peek(0) == 0x302;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1cc;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s22, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 75
    * Starting at 0x302
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x35a

    requires s0.stack[3] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x35a;
      assert s1.Peek(3) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02fc);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x031c);
      assert s11.Peek(0) == 0x31c;
      assert s11.Peek(4) == 0x2fc;
      assert s11.Peek(7) == 0x35a;
      assert s11.Peek(9) == 0x1cc;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x160e);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s16, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x31c

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x35a

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31c;
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x35a;
      assert s1.Peek(9) == 0x1cc;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0x31c;
      assert s11.Peek(9) == 0x2fc;
      assert s11.Peek(12) == 0x35a;
      assert s11.Peek(14) == 0x1cc;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s12, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x31c

    requires s0.stack[8] == 0x2fc

    requires s0.stack[11] == 0x35a

    requires s0.stack[13] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x31c;
      assert s1.Peek(8) == 0x2fc;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(13) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s15(s5, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x31c

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x35a

    requires s0.stack[16] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x31c;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x35a;
      assert s1.Peek(16) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s7, gas - 1)
      else
        ExecuteFromCFGNode_s16(s7, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x31c

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x35a

    requires s0.stack[16] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x31c;
      assert s1.Peek(12) == 0x2fc;
      assert s1.Peek(15) == 0x35a;
      assert s1.Peek(17) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0x31c;
      assert s11.Peek(12) == 0x2fc;
      assert s11.Peek(15) == 0x35a;
      assert s11.Peek(17) == 0x1cc;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s14, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x31c

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x35a

    requires s0.stack[16] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x31c;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x35a;
      assert s1.Peek(16) == 0x1cc;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0x31c;
      assert s11.Peek(8) == 0x2fc;
      assert s11.Peek(11) == 0x35a;
      assert s11.Peek(13) == 0x1cc;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s14, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x31c

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x31c;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x35a;
      assert s1.Peek(11) == 0x1cc;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s8, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 76
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x35a

    requires s0.stack[6] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x35a;
      assert s1.Peek(6) == 0x1cc;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x2fc;
      assert s11.Peek(5) == 0x35a;
      assert s11.Peek(7) == 0x1cc;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x1094);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s21, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 143
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x35a

    requires s0.stack[6] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x35a;
      assert s1.Peek(6) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x35a;
      assert s11.Peek(11) == 0x1cc;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x2fc;
      assert s21.Peek(7) == 0x35a;
      assert s21.Peek(9) == 0x1cc;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x2fc;
      assert s31.Peek(12) == 0x35a;
      assert s31.Peek(14) == 0x1cc;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1108);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s41, gas - 1)
      else
        ExecuteFromCFGNode_s21(s41, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 144
    * Starting at 0x10ff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x35a;
      assert s1.Peek(12) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 22
    * Segment Id for this node is: 145
    * Starting at 0x1108
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1108 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x35a;
      assert s1.Peek(11) == 0x1cc;
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
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x35a;
      assert s11.Peek(11) == 0x1cc;
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
      assert s21.Peek(5) == 0x2fc;
      assert s21.Peek(8) == 0x35a;
      assert s21.Peek(10) == 0x1cc;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1644);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s28, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 209
    * Starting at 0x1644
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x2fc

    requires s0.stack[8] == 0x35a

    requires s0.stack[10] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x2fc;
      assert s1.Peek(8) == 0x35a;
      assert s1.Peek(10) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1656);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s10, gas - 1)
      else
        ExecuteFromCFGNode_s24(s10, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 210
    * Starting at 0x1652
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x35a;
      assert s1.Peek(12) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 211
    * Starting at 0x1656
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1656 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x35a;
      assert s1.Peek(11) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x14cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s7, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 176
    * Starting at 0x14cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x35a

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x2fc;
      assert s1.Peek(12) == 0x35a;
      assert s1.Peek(14) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s8, gas - 1)
      else
        ExecuteFromCFGNode_s27(s8, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 177
    * Starting at 0x14d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x35a

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x2fc;
      assert s1.Peek(13) == 0x35a;
      assert s1.Peek(15) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 28
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x35a

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x2fc;
      assert s1.Peek(12) == 0x35a;
      assert s1.Peek(14) == 0x1cc;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s3, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x2fc

    requires s0.stack[10] == 0x35a

    requires s0.stack[12] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x35a;
      assert s1.Peek(12) == 0x1cc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s7, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x35a

    requires s0.stack[8] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x35a;
      assert s1.Peek(8) == 0x1cc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s6, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x35a

    requires s0.stack[5] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35a;
      assert s1.Peek(5) == 0x1cc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s6, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 78
    * Starting at 0x35a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1cc;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s5, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 45
    * Starting at 0x1cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1cc as nat
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
      var s11 := Push2(s10, 0x01b0);
      assert s11.Peek(0) == 0x1b0;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s12, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 42
    * Starting at 0x1b0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b0 as nat
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

  /** Node 35
    * Segment Id for this node is: 70
    * Starting at 0x2b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0f7c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s4, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 138
    * Starting at 0xf7c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x18);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e6e6f64652e6665652e6d6178696d756d0000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 126
    * Starting at 0xd18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x35a

    requires s0.stack[3] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x35a;
      assert s1.Peek(3) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02fc);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d32);
      assert s11.Peek(0) == 0xd32;
      assert s11.Peek(4) == 0x2fc;
      assert s11.Peek(7) == 0x35a;
      assert s11.Peek(9) == 0x1e4;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x160e);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s16, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0xd32

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x35a

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd32;
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x35a;
      assert s1.Peek(9) == 0x1e4;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0xd32;
      assert s11.Peek(9) == 0x2fc;
      assert s11.Peek(12) == 0x35a;
      assert s11.Peek(14) == 0x1e4;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s12, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0xd32

    requires s0.stack[8] == 0x2fc

    requires s0.stack[11] == 0x35a

    requires s0.stack[13] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0xd32;
      assert s1.Peek(8) == 0x2fc;
      assert s1.Peek(11) == 0x35a;
      assert s1.Peek(13) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s40(s5, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xd32

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x35a

    requires s0.stack[16] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xd32;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x35a;
      assert s1.Peek(16) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s7, gas - 1)
      else
        ExecuteFromCFGNode_s41(s7, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xd32

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x35a

    requires s0.stack[16] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0xd32;
      assert s1.Peek(12) == 0x2fc;
      assert s1.Peek(15) == 0x35a;
      assert s1.Peek(17) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0xd32;
      assert s11.Peek(12) == 0x2fc;
      assert s11.Peek(15) == 0x35a;
      assert s11.Peek(17) == 0x1e4;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s14, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xd32

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x35a

    requires s0.stack[16] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xd32;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x35a;
      assert s1.Peek(16) == 0x1e4;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0xd32;
      assert s11.Peek(8) == 0x2fc;
      assert s11.Peek(11) == 0x35a;
      assert s11.Peek(13) == 0x1e4;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s14, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0xd32

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd32;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x35a;
      assert s1.Peek(11) == 0x1e4;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s8, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 127
    * Starting at 0xd32
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd32 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x35a

    requires s0.stack[6] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x35a;
      assert s1.Peek(6) == 0x1e4;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x2fc;
      assert s11.Peek(5) == 0x35a;
      assert s11.Peek(7) == 0x1e4;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x12b9);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s21, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 156
    * Starting at 0x12b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x35a

    requires s0.stack[6] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x35a;
      assert s1.Peek(6) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0xbd02d0f500000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x35a;
      assert s11.Peek(11) == 0x1e4;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x2fc;
      assert s21.Peek(7) == 0x35a;
      assert s21.Peek(9) == 0x1e4;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0xbd02d0f5);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x2fc;
      assert s31.Peek(12) == 0x35a;
      assert s31.Peek(14) == 0x1e4;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x132d);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s41, gas - 1)
      else
        ExecuteFromCFGNode_s46(s41, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 157
    * Starting at 0x1324
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x35a;
      assert s1.Peek(12) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 47
    * Segment Id for this node is: 158
    * Starting at 0x132d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x35a;
      assert s1.Peek(11) == 0x1e4;
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
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x35a;
      assert s11.Peek(11) == 0x1e4;
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
      assert s21.Peek(5) == 0x2fc;
      assert s21.Peek(8) == 0x35a;
      assert s21.Peek(10) == 0x1e4;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1693);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s28, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 213
    * Starting at 0x1693
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1693 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x2fc

    requires s0.stack[8] == 0x35a

    requires s0.stack[10] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x2fc;
      assert s1.Peek(8) == 0x35a;
      assert s1.Peek(10) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x16a5);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s10, gas - 1)
      else
        ExecuteFromCFGNode_s49(s10, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 214
    * Starting at 0x16a1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x35a;
      assert s1.Peek(12) == 0x1e4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 50
    * Segment Id for this node is: 215
    * Starting at 0x16a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x35a

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x35a;
      assert s1.Peek(11) == 0x1e4;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s7, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x35a

    requires s0.stack[8] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x35a;
      assert s1.Peek(8) == 0x1e4;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s6, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x35a

    requires s0.stack[5] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x35a;
      assert s1.Peek(5) == 0x1e4;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s6, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 78
    * Starting at 0x35a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1e4;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s5, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 47
    * Starting at 0x1e4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e4 as nat
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
      var s9 := Push2(s8, 0x01b0);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s10, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 69
    * Starting at 0x2af
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0f3c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s4, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 137
    * Starting at 0xf3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x1e);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e726574682e636f6c6c61746572616c2e7461726765740000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 10
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0xcecaef21);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x028c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s6, gas - 1)
      else
        ExecuteFromCFGNode_s58(s6, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xd6cd921e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0294);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s5, gas - 1)
      else
        ExecuteFromCFGNode_s59(s5, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xd7c8953c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x02a7);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s5, gas - 1)
      else
        ExecuteFromCFGNode_s60(s5, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
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

  /** Node 61
    * Segment Id for this node is: 68
    * Starting at 0x2a7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01cc);
      var s3 := Push2(s2, 0x0efc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s4, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 136
    * Starting at 0xefc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1cc;
      var s12 := Push1(s11, 0x1d);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e7375626d69742e7072696365732e656e61626c6564000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0302);
      assert s21.Peek(0) == 0x302;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1cc;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s22, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 66
    * Starting at 0x294
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x294 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020d);
      var s3 := Push2(s2, 0x02a2);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1597);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s7, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 194
    * Starting at 0x1597
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1597 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2a2

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a2;
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x15aa);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s11, gas - 1)
      else
        ExecuteFromCFGNode_s65(s11, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 195
    * Starting at 0x15a6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15a6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2a2

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x2a2;
      assert s1.Peek(6) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 66
    * Segment Id for this node is: 196
    * Starting at 0x15aa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15aa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x2a2

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2a2;
      assert s1.Peek(5) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x15c1);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s68(s9, gas - 1)
      else
        ExecuteFromCFGNode_s67(s9, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 197
    * Starting at 0x15bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2a2

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x2a2;
      assert s1.Peek(7) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 68
    * Segment Id for this node is: 198
    * Starting at 0x15c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2a2

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2a2;
      assert s1.Peek(6) == 0x20d;
      var s2 := Push2(s1, 0x15cd);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x13e5);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s8, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 161
    * Starting at 0x13e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x15cd

    requires s0.stack[8] == 0x2a2

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x15cd;
      assert s1.Peek(8) == 0x2a2;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x13f6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s9, gas - 1)
      else
        ExecuteFromCFGNode_s70(s9, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 162
    * Starting at 0x13f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x15cd

    requires s0.stack[9] == 0x2a2

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x15cd;
      assert s1.Peek(10) == 0x2a2;
      assert s1.Peek(11) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 71
    * Segment Id for this node is: 163
    * Starting at 0x13f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x15cd

    requires s0.stack[9] == 0x2a2

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x15cd;
      assert s1.Peek(9) == 0x2a2;
      assert s1.Peek(10) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1411);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s74(s10, gas - 1)
      else
        ExecuteFromCFGNode_s72(s10, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 164
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x15cd

    requires s0.stack[11] == 0x2a2

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1411);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x15cd;
      assert s1.Peek(12) == 0x2a2;
      assert s1.Peek(13) == 0x20d;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1411

    requires s0.stack[6] == 0x15cd

    requires s0.stack[12] == 0x2a2

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x15cd;
      assert s1.Peek(12) == 0x2a2;
      assert s1.Peek(13) == 0x20d;
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

  /** Node 74
    * Segment Id for this node is: 165
    * Starting at 0x1411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x15cd

    requires s0.stack[11] == 0x2a2

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x15cd;
      assert s1.Peek(11) == 0x2a2;
      assert s1.Peek(12) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x15cd;
      assert s11.Peek(15) == 0x2a2;
      assert s11.Peek(16) == 0x20d;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x15cd;
      assert s21.Peek(16) == 0x2a2;
      assert s21.Peek(17) == 0x20d;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x1457);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s77(s26, gas - 1)
      else
        ExecuteFromCFGNode_s75(s26, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 166
    * Starting at 0x1450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x15cd

    requires s0.stack[13] == 0x2a2

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1457);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x15cd;
      assert s1.Peek(14) == 0x2a2;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s3, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x1457

    requires s0.stack[8] == 0x15cd

    requires s0.stack[14] == 0x2a2

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x15cd;
      assert s1.Peek(14) == 0x2a2;
      assert s1.Peek(15) == 0x20d;
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

  /** Node 77
    * Segment Id for this node is: 167
    * Starting at 0x1457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x15cd

    requires s0.stack[13] == 0x2a2

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x15cd;
      assert s1.Peek(13) == 0x2a2;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x15cd;
      assert s11.Peek(17) == 0x2a2;
      assert s11.Peek(18) == 0x20d;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x1470);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s17, gas - 1)
      else
        ExecuteFromCFGNode_s78(s17, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 168
    * Starting at 0x146c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x15cd

    requires s0.stack[13] == 0x2a2

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x15cd;
      assert s1.Peek(14) == 0x2a2;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 79
    * Segment Id for this node is: 169
    * Starting at 0x1470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x15cd

    requires s0.stack[13] == 0x2a2

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x15cd;
      assert s1.Peek(13) == 0x2a2;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x15cd;
      assert s11.Peek(15) == 0x2a2;
      assert s11.Peek(16) == 0x20d;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x15cd;
      assert s21.Peek(11) == 0x2a2;
      assert s21.Peek(12) == 0x20d;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s28, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 199
    * Starting at 0x15cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x2a2

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2a2;
      assert s1.Peek(7) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push2(s8, 0x1525);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x1575);
      assert s11.Peek(0) == 0x1575;
      assert s11.Peek(2) == 0x1525;
      assert s11.Peek(8) == 0x2a2;
      assert s11.Peek(9) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s12, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 192
    * Starting at 0x1575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1525

    requires s0.stack[7] == 0x2a2

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1525;
      assert s1.Peek(7) == 0x2a2;
      assert s1.Peek(8) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s8, gas - 1)
      else
        ExecuteFromCFGNode_s82(s8, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 193
    * Starting at 0x1593
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1525

    requires s0.stack[7] == 0x2a2

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1525;
      assert s1.Peek(8) == 0x2a2;
      assert s1.Peek(9) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 83
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1525

    requires s0.stack[7] == 0x2a2

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1525;
      assert s1.Peek(7) == 0x2a2;
      assert s1.Peek(8) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s3, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 185
    * Starting at 0x1525
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1525 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x2a2

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2a2;
      assert s1.Peek(6) == 0x20d;
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
      ExecuteFromCFGNode_s85(s11, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 67
    * Starting at 0x2a2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x0d8d);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s3, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 129
    * Starting at 0xd8d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x0dcb);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x031c);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x31c;
      assert s11.Peek(4) == 0xdcb;
      assert s11.Peek(7) == 0x20d;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s21, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 76
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xdcb

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdcb;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xdcb;
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x1094);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s21, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 143
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xdcb

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xdcb;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xdcb;
      assert s11.Peek(9) == 0x20d;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0xdcb;
      assert s21.Peek(7) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0xdcb;
      assert s31.Peek(12) == 0x20d;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1108);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s90(s41, gas - 1)
      else
        ExecuteFromCFGNode_s89(s41, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 144
    * Starting at 0x10ff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0xdcb

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xdcb;
      assert s1.Peek(10) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 90
    * Segment Id for this node is: 145
    * Starting at 0x1108
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1108 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0xdcb

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xdcb;
      assert s1.Peek(9) == 0x20d;
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
      assert s11.Peek(6) == 0xdcb;
      assert s11.Peek(9) == 0x20d;
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
      assert s21.Peek(5) == 0xdcb;
      assert s21.Peek(8) == 0x20d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1644);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s28, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 209
    * Starting at 0x1644
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0xdcb

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0xdcb;
      assert s1.Peek(8) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1656);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s10, gas - 1)
      else
        ExecuteFromCFGNode_s92(s10, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 210
    * Starting at 0x1652
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0xdcb

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0xdcb;
      assert s1.Peek(10) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 93
    * Segment Id for this node is: 211
    * Starting at 0x1656
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1656 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0xdcb

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0xdcb;
      assert s1.Peek(9) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x14cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s7, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 176
    * Starting at 0x14cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0xdcb

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0xdcb;
      assert s1.Peek(12) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s8, gas - 1)
      else
        ExecuteFromCFGNode_s95(s8, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 177
    * Starting at 0x14d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0xdcb

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0xdcb;
      assert s1.Peek(13) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 96
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0xdcb

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0xdcb;
      assert s1.Peek(12) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s3, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0xdcb

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0xdcb;
      assert s1.Peek(10) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s7, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0xdcb

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xdcb;
      assert s1.Peek(6) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s6, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 130
    * Starting at 0xdcb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdcb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0ec8);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s4, gas - 1)
      else
        ExecuteFromCFGNode_s100(s4, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 131
    * Starting at 0xdd1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdd1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0e25);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xe25;
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push32(s17, 0x726f636b657444414f50726f746f636f6c50726f706f73616c73000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0xe25;
      assert s21.Peek(5) == 0x20d;
      var s22 := Push2(s21, 0x112c);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s101(s23, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 146
    * Starting at 0x112c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xe25

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe25;
      assert s1.Peek(5) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1143);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x02e1);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2e1;
      assert s11.Peek(3) == 0x1143;
      assert s11.Peek(7) == 0xe25;
      assert s11.Peek(11) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x1661);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s14, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 212
    * Starting at 0x1661
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1661 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x2e1

    requires s0.stack[3] == 0x1143

    requires s0.stack[7] == 0xe25

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2e1;
      assert s1.Peek(3) == 0x1143;
      assert s1.Peek(7) == 0xe25;
      assert s1.Peek(11) == 0x20d;
      var s2 := Push32(s1, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x163d);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x163d;
      assert s11.Peek(7) == 0x2e1;
      assert s11.Peek(8) == 0x1143;
      assert s11.Peek(12) == 0xe25;
      assert s11.Peek(16) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s12, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x163d

    requires s0.stack[6] == 0x2e1

    requires s0.stack[7] == 0x1143

    requires s0.stack[11] == 0xe25

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(6) == 0x2e1;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0xe25;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s104(s5, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0xe25

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x163d;
      assert s1.Peek(9) == 0x2e1;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0xe25;
      assert s1.Peek(18) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s106(s7, gas - 1)
      else
        ExecuteFromCFGNode_s105(s7, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0xe25

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x163d;
      assert s1.Peek(10) == 0x2e1;
      assert s1.Peek(11) == 0x1143;
      assert s1.Peek(15) == 0xe25;
      assert s1.Peek(19) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x163d;
      assert s11.Peek(10) == 0x2e1;
      assert s11.Peek(11) == 0x1143;
      assert s11.Peek(15) == 0xe25;
      assert s11.Peek(19) == 0x20d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s14, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0xe25

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x163d;
      assert s1.Peek(9) == 0x2e1;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0xe25;
      assert s1.Peek(18) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x163d;
      assert s11.Peek(6) == 0x2e1;
      assert s11.Peek(7) == 0x1143;
      assert s11.Peek(11) == 0xe25;
      assert s11.Peek(15) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s14, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x2e1

    requires s0.stack[5] == 0x1143

    requires s0.stack[9] == 0xe25

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2e1;
      assert s1.Peek(5) == 0x1143;
      assert s1.Peek(9) == 0xe25;
      assert s1.Peek(13) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s108(s7, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 73
    * Starting at 0x2e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1143

    requires s0.stack[5] == 0xe25

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1143;
      assert s1.Peek(5) == 0xe25;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x1143;
      assert s11.Peek(6) == 0xe25;
      assert s11.Peek(10) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0ffc);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s21, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 140
    * Starting at 0xffc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1143

    requires s0.stack[5] == 0xe25

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1143;
      assert s1.Peek(5) == 0xe25;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x1143;
      assert s11.Peek(10) == 0xe25;
      assert s11.Peek(14) == 0x20d;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x1143;
      assert s21.Peek(8) == 0xe25;
      assert s21.Peek(12) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x1143;
      assert s31.Peek(13) == 0xe25;
      assert s31.Peek(17) == 0x20d;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1070);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s41, gas - 1)
      else
        ExecuteFromCFGNode_s110(s41, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 141
    * Starting at 0x1067
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0xe25

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0xe25;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 111
    * Segment Id for this node is: 142
    * Starting at 0x1070
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0xe25

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1143;
      assert s1.Peek(10) == 0xe25;
      assert s1.Peek(14) == 0x20d;
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
      assert s11.Peek(6) == 0x1143;
      assert s11.Peek(10) == 0xe25;
      assert s11.Peek(14) == 0x20d;
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
      assert s21.Peek(5) == 0x1143;
      assert s21.Peek(9) == 0xe25;
      assert s21.Peek(13) == 0x20d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1620);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s28, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 205
    * Starting at 0x1620
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x1143

    requires s0.stack[9] == 0xe25

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x1143;
      assert s1.Peek(9) == 0xe25;
      assert s1.Peek(13) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1632);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s10, gas - 1)
      else
        ExecuteFromCFGNode_s113(s10, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 206
    * Starting at 0x162e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0xe25

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0xe25;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 207
    * Starting at 0x1632
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0xe25

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x1143;
      assert s1.Peek(10) == 0xe25;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1575);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s7, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 192
    * Starting at 0x1575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0xe25

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1143;
      assert s1.Peek(13) == 0xe25;
      assert s1.Peek(17) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s117(s8, gas - 1)
      else
        ExecuteFromCFGNode_s116(s8, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 193
    * Starting at 0x1593
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0xe25

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0xe25;
      assert s1.Peek(18) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 117
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0xe25

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1143;
      assert s1.Peek(13) == 0xe25;
      assert s1.Peek(17) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s3, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x1143

    requires s0.stack[11] == 0xe25

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0xe25;
      assert s1.Peek(15) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s7, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1143

    requires s0.stack[7] == 0xe25

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1143;
      assert s1.Peek(7) == 0xe25;
      assert s1.Peek(11) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 147
    * Starting at 0x1143
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xe25

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe25;
      assert s1.Peek(8) == 0x20d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x02fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s123(s8, gas - 1)
      else
        ExecuteFromCFGNode_s121(s8, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 148
    * Starting at 0x1161
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1161 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe25

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xe25;
      assert s1.Peek(8) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x12);
      assert s11.Peek(5) == 0xe25;
      assert s11.Peek(9) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0xe25;
      assert s21.Peek(9) == 0x20d;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x04d6);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s24, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 85
    * Starting at 0x4d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xe25

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe25;
      assert s1.Peek(8) == 0x20d;
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

  /** Node 123
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe25

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe25;
      assert s1.Peek(7) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s124(s6, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 132
    * Starting at 0xe25
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe25 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0ec8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s6, gas - 1)
      else
        ExecuteFromCFGNode_s125(s6, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 133
    * Starting at 0xe41
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x39);
      assert s11.Peek(4) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f6e6c792044414f2050726f746f636f6c2050726f706f73616c7320636f6e74);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x726163742063616e2075706461746520612073657474696e6700000000000000);
      assert s21.Peek(4) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s29, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 85
    * Starting at 0x4d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
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

  /** Node 127
    * Segment Id for this node is: 134
    * Starting at 0xec8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xec8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x0513);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0ee0);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0xee0;
      assert s11.Peek(4) == 0x513;
      assert s11.Peek(7) == 0x20d;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x160e);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s15, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xee0

    requires s0.stack[4] == 0x513

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xee0;
      assert s1.Peek(4) == 0x513;
      assert s1.Peek(7) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0xee0;
      assert s11.Peek(9) == 0x513;
      assert s11.Peek(12) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s12, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0xee0

    requires s0.stack[8] == 0x513

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0xee0;
      assert s1.Peek(8) == 0x513;
      assert s1.Peek(11) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s130(s5, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xee0

    requires s0.stack[11] == 0x513

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xee0;
      assert s1.Peek(11) == 0x513;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s132(s7, gas - 1)
      else
        ExecuteFromCFGNode_s131(s7, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xee0

    requires s0.stack[11] == 0x513

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0xee0;
      assert s1.Peek(12) == 0x513;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0xee0;
      assert s11.Peek(12) == 0x513;
      assert s11.Peek(15) == 0x20d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s14, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xee0

    requires s0.stack[11] == 0x513

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xee0;
      assert s1.Peek(11) == 0x513;
      assert s1.Peek(14) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0xee0;
      assert s11.Peek(8) == 0x513;
      assert s11.Peek(11) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s14, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xee0

    requires s0.stack[6] == 0x513

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xee0;
      assert s1.Peek(6) == 0x513;
      assert s1.Peek(9) == 0x20d;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s134(s8, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 135
    * Starting at 0xee0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xee0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x513

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x513;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x513;
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup3(s19);
      var s21 := Push2(s20, 0x1351);
      assert s21.Peek(0) == 0x1351;
      assert s21.Peek(3) == 0x513;
      assert s21.Peek(6) == 0x20d;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s135(s22, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 159
    * Starting at 0x1351
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1351 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x513

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x513;
      assert s1.Peek(5) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xca446dd900000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x513;
      assert s11.Peek(8) == 0x20d;
      var s12 := Dup5(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push20(s14, 0xffffffffffffffffffffffffffffffffffffffff);
      var s16 := Dup4(s15);
      var s17 := Dup2(s16);
      var s18 := And(s17);
      var s19 := Push1(s18, 0x24);
      var s20 := Dup4(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x513;
      assert s21.Peek(10) == 0x20d;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x0100);
      var s24 := Swap1(s23);
      var s25 := Swap3(s24);
      var s26 := Div(s25);
      var s27 := Swap1(s26);
      var s28 := Swap2(s27);
      var s29 := And(s28);
      var s30 := Swap1(s29);
      var s31 := Push4(s30, 0xca446dd9);
      assert s31.Peek(5) == 0x513;
      assert s31.Peek(8) == 0x20d;
      var s32 := Swap1(s31);
      var s33 := Push1(s32, 0x44);
      var s34 := Add(s33);
      var s35 := Push2(s34, 0x1221);
      var s36 := Jump(s35);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s36, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 150
    * Starting at 0x1221
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1221 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[5] == 0x513

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x513;
      assert s1.Peek(8) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup8(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(12) == 0x513;
      assert s11.Peek(15) == 0x20d;
      var s12 := ExtCodeSize(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x123b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s17, gas - 1)
      else
        ExecuteFromCFGNode_s137(s17, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 151
    * Starting at 0x1237
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x513

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x513;
      assert s1.Peek(16) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 138
    * Segment Id for this node is: 152
    * Starting at 0x123b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x513

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x513;
      assert s1.Peek(15) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x124f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s140(s9, gas - 1)
      else
        ExecuteFromCFGNode_s139(s9, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 153
    * Starting at 0x1246
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1246 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x513

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x513;
      assert s1.Peek(10) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 140
    * Segment Id for this node is: 154
    * Starting at 0x124f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x513

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x513;
      assert s1.Peek(9) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s8, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 88
    * Starting at 0x513
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x513 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s4, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 51
    * Starting at 0x20d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20d as nat
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

  /** Node 143
    * Segment Id for this node is: 65
    * Starting at 0x28c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0d4d);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s4, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 128
    * Starting at 0xd4d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x1a);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e726574682e6465706f7369742e64656c6179000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 14
    * Starting at 0x8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0xac93f57f);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00bd);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s6, gas - 1)
      else
        ExecuteFromCFGNode_s146(s6, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 15
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xac93f57f);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0269);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s5, gas - 1)
      else
        ExecuteFromCFGNode_s147(s5, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xadd7a12d);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0271);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s5, gas - 1)
      else
        ExecuteFromCFGNode_s148(s5, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xc56710ff);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0279);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s5, gas - 1)
      else
        ExecuteFromCFGNode_s149(s5, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
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

  /** Node 150
    * Segment Id for this node is: 63
    * Starting at 0x279
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x279 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0287);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1490);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s7, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 170
    * Starting at 0x1490
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1490 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x287

    requires s0.stack[3] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x287;
      assert s1.Peek(3) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x14a2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s10, gas - 1)
      else
        ExecuteFromCFGNode_s152(s10, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 171
    * Starting at 0x149e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x287

    requires s0.stack[4] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x287;
      assert s1.Peek(5) == 0x1e4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 153
    * Segment Id for this node is: 172
    * Starting at 0x14a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x287

    requires s0.stack[4] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x287;
      assert s1.Peek(4) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s9, gas - 1)
      else
        ExecuteFromCFGNode_s154(s9, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 173
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x287

    requires s0.stack[5] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x287;
      assert s1.Peek(6) == 0x1e4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 155
    * Segment Id for this node is: 174
    * Starting at 0x14b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x287

    requires s0.stack[5] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x287;
      assert s1.Peek(5) == 0x1e4;
      var s2 := Push2(s1, 0x14c5);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x13e5);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s8, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 161
    * Starting at 0x13e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x287

    requires s0.stack[8] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x287;
      assert s1.Peek(8) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x13f6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s158(s9, gas - 1)
      else
        ExecuteFromCFGNode_s157(s9, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 162
    * Starting at 0x13f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x14c5

    requires s0.stack[8] == 0x287

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x14c5;
      assert s1.Peek(9) == 0x287;
      assert s1.Peek(10) == 0x1e4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 158
    * Segment Id for this node is: 163
    * Starting at 0x13f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x14c5

    requires s0.stack[8] == 0x287

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x14c5;
      assert s1.Peek(8) == 0x287;
      assert s1.Peek(9) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1411);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s10, gas - 1)
      else
        ExecuteFromCFGNode_s159(s10, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 164
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x287

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1411);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x287;
      assert s1.Peek(12) == 0x1e4;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s3, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1411

    requires s0.stack[6] == 0x14c5

    requires s0.stack[11] == 0x287

    requires s0.stack[12] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x287;
      assert s1.Peek(12) == 0x1e4;
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

  /** Node 161
    * Segment Id for this node is: 165
    * Starting at 0x1411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x287

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x287;
      assert s1.Peek(11) == 0x1e4;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x14c5;
      assert s11.Peek(14) == 0x287;
      assert s11.Peek(15) == 0x1e4;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x14c5;
      assert s21.Peek(15) == 0x287;
      assert s21.Peek(16) == 0x1e4;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x1457);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s164(s26, gas - 1)
      else
        ExecuteFromCFGNode_s162(s26, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 166
    * Starting at 0x1450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x287

    requires s0.stack[13] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1457);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x287;
      assert s1.Peek(14) == 0x1e4;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s163(s3, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x1457

    requires s0.stack[8] == 0x14c5

    requires s0.stack[13] == 0x287

    requires s0.stack[14] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x287;
      assert s1.Peek(14) == 0x1e4;
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

  /** Node 164
    * Segment Id for this node is: 167
    * Starting at 0x1457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x287

    requires s0.stack[13] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x14c5;
      assert s1.Peek(12) == 0x287;
      assert s1.Peek(13) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x14c5;
      assert s11.Peek(16) == 0x287;
      assert s11.Peek(17) == 0x1e4;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x1470);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s166(s17, gas - 1)
      else
        ExecuteFromCFGNode_s165(s17, gas - 1)
  }

  /** Node 165
    * Segment Id for this node is: 168
    * Starting at 0x146c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x287

    requires s0.stack[13] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x287;
      assert s1.Peek(14) == 0x1e4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 166
    * Segment Id for this node is: 169
    * Starting at 0x1470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x287

    requires s0.stack[13] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x14c5;
      assert s1.Peek(12) == 0x287;
      assert s1.Peek(13) == 0x1e4;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x14c5;
      assert s11.Peek(14) == 0x287;
      assert s11.Peek(15) == 0x1e4;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x14c5;
      assert s21.Peek(10) == 0x287;
      assert s21.Peek(11) == 0x1e4;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s28, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x287

    requires s0.stack[6] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x287;
      assert s1.Peek(6) == 0x1e4;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s168(s8, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 64
    * Starting at 0x287
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x287 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1e4;
      var s2 := Push2(s1, 0x0d18);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s3, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 126
    * Starting at 0xd18
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd18 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02fc);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0d32);
      assert s11.Peek(0) == 0xd32;
      assert s11.Peek(4) == 0x2fc;
      assert s11.Peek(7) == 0x1e4;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x160e);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s16, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xd32

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xd32;
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1e4;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0xd32;
      assert s11.Peek(9) == 0x2fc;
      assert s11.Peek(12) == 0x1e4;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s171(s12, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0xd32

    requires s0.stack[8] == 0x2fc

    requires s0.stack[11] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0xd32;
      assert s1.Peek(8) == 0x2fc;
      assert s1.Peek(11) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s172(s5, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xd32

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xd32;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s7, gas - 1)
      else
        ExecuteFromCFGNode_s173(s7, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xd32

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0xd32;
      assert s1.Peek(12) == 0x2fc;
      assert s1.Peek(15) == 0x1e4;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0xd32;
      assert s11.Peek(12) == 0x2fc;
      assert s11.Peek(15) == 0x1e4;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s14, gas - 1)
  }

  /** Node 174
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xd32

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xd32;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x1e4;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0xd32;
      assert s11.Peek(8) == 0x2fc;
      assert s11.Peek(11) == 0x1e4;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s14, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xd32

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xd32;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1e4;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s8, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 127
    * Starting at 0xd32
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd32 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x1e4;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x2fc;
      assert s11.Peek(5) == 0x1e4;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x12b9);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s21, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 156
    * Starting at 0x12b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0xbd02d0f500000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x1e4;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x2fc;
      assert s21.Peek(7) == 0x1e4;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0xbd02d0f5);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x2fc;
      assert s31.Peek(12) == 0x1e4;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x132d);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s41, gas - 1)
      else
        ExecuteFromCFGNode_s178(s41, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 157
    * Starting at 0x1324
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1324 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 179
    * Segment Id for this node is: 158
    * Starting at 0x132d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x132d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1e4;
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
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x1e4;
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
      assert s21.Peek(5) == 0x2fc;
      assert s21.Peek(8) == 0x1e4;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1693);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s28, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 213
    * Starting at 0x1693
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1693 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x2fc

    requires s0.stack[8] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x2fc;
      assert s1.Peek(8) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x16a5);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s10, gas - 1)
      else
        ExecuteFromCFGNode_s181(s10, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 214
    * Starting at 0x16a1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1e4;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 182
    * Segment Id for this node is: 215
    * Starting at 0x16a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1e4;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s183(s7, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x1e4;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s6, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1e4;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s6, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 62
    * Starting at 0x271
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x271 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0cdc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s186(s4, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 125
    * Starting at 0xcdc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x18);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e6e6f64652e6665652e6d696e696d756d0000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s37(s20, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 61
    * Starting at 0x269
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x269 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0c9c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s4, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 124
    * Starting at 0xc9c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x1d);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e6e6f64652e6665652e64656d616e642e72616e6765000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 19
    * Starting at 0xbd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x97fa4f40);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0259);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s6, gas - 1)
      else
        ExecuteFromCFGNode_s190(s6, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 20
    * Starting at 0xc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xa03eec10);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0261);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s192(s5, gas - 1)
      else
        ExecuteFromCFGNode_s191(s5, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
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

  /** Node 192
    * Segment Id for this node is: 60
    * Starting at 0x261
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x261 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0c5c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s193(s4, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 123
    * Starting at 0xc5c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc5c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x17);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e6e6f64652e6665652e746172676574000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 59
    * Starting at 0x259
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x259 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0c1c);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s4, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 122
    * Starting at 0xc1c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x18);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e70656e616c74792e7065722e726174650000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 22
    * Starting at 0xd8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x31607418);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x012f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s311(s6, gas - 1)
      else
        ExecuteFromCFGNode_s197(s6, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 23
    * Starting at 0xe4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x58485df6);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0114);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s303(s5, gas - 1)
      else
        ExecuteFromCFGNode_s198(s5, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 24
    * Starting at 0xef
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x58485df6);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0236);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s5, gas - 1)
      else
        ExecuteFromCFGNode_s199(s5, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 25
    * Starting at 0xfa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x5e9d4044);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x023e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s5, gas - 1)
      else
        ExecuteFromCFGNode_s200(s5, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 26
    * Starting at 0x105
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x63ed62da);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0251);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s5, gas - 1)
      else
        ExecuteFromCFGNode_s201(s5, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 27
    * Starting at 0x110
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110 as nat
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

  /** Node 202
    * Segment Id for this node is: 58
    * Starting at 0x251
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01cc);
      var s3 := Push2(s2, 0x0bdc);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s203(s4, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 121
    * Starting at 0xbdc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbdc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1cc;
      var s12 := Push1(s11, 0x1e);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e7375626d69742e726577617264732e656e61626c65640000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0302);
      assert s21.Peek(0) == 0x302;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1cc;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s22, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 56
    * Starting at 0x23e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020d);
      var s3 := Push2(s2, 0x024c);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1530);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s205(s7, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 186
    * Starting at 0x1530
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1530 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x24c

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x24c;
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x1543);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s11, gas - 1)
      else
        ExecuteFromCFGNode_s206(s11, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 187
    * Starting at 0x153f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x153f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x24c

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x24c;
      assert s1.Peek(6) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 207
    * Segment Id for this node is: 188
    * Starting at 0x1543
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1543 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x24c

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x24c;
      assert s1.Peek(5) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x155a);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s9, gas - 1)
      else
        ExecuteFromCFGNode_s208(s9, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 189
    * Starting at 0x1556
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x24c

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x24c;
      assert s1.Peek(7) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 209
    * Segment Id for this node is: 190
    * Starting at 0x155a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x155a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x24c

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x24c;
      assert s1.Peek(6) == 0x20d;
      var s2 := Push2(s1, 0x1566);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x13e5);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s210(s8, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 161
    * Starting at 0x13e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1566

    requires s0.stack[8] == 0x24c

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1566;
      assert s1.Peek(8) == 0x24c;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x13f6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s212(s9, gas - 1)
      else
        ExecuteFromCFGNode_s211(s9, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 162
    * Starting at 0x13f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1566

    requires s0.stack[9] == 0x24c

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1566;
      assert s1.Peek(10) == 0x24c;
      assert s1.Peek(11) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 212
    * Segment Id for this node is: 163
    * Starting at 0x13f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1566

    requires s0.stack[9] == 0x24c

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1566;
      assert s1.Peek(9) == 0x24c;
      assert s1.Peek(10) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1411);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s215(s10, gas - 1)
      else
        ExecuteFromCFGNode_s213(s10, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 164
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1566

    requires s0.stack[11] == 0x24c

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1411);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x1566;
      assert s1.Peek(12) == 0x24c;
      assert s1.Peek(13) == 0x20d;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s3, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1411

    requires s0.stack[6] == 0x1566

    requires s0.stack[12] == 0x24c

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x1566;
      assert s1.Peek(12) == 0x24c;
      assert s1.Peek(13) == 0x20d;
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

  /** Node 215
    * Segment Id for this node is: 165
    * Starting at 0x1411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1566

    requires s0.stack[11] == 0x24c

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1566;
      assert s1.Peek(11) == 0x24c;
      assert s1.Peek(12) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x1566;
      assert s11.Peek(15) == 0x24c;
      assert s11.Peek(16) == 0x20d;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x1566;
      assert s21.Peek(16) == 0x24c;
      assert s21.Peek(17) == 0x20d;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x1457);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s26, gas - 1)
      else
        ExecuteFromCFGNode_s216(s26, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 166
    * Starting at 0x1450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1566

    requires s0.stack[13] == 0x24c

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1457);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x1566;
      assert s1.Peek(14) == 0x24c;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s3, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x1457

    requires s0.stack[8] == 0x1566

    requires s0.stack[14] == 0x24c

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x1566;
      assert s1.Peek(14) == 0x24c;
      assert s1.Peek(15) == 0x20d;
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

  /** Node 218
    * Segment Id for this node is: 167
    * Starting at 0x1457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1566

    requires s0.stack[13] == 0x24c

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1566;
      assert s1.Peek(13) == 0x24c;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1566;
      assert s11.Peek(17) == 0x24c;
      assert s11.Peek(18) == 0x20d;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x1470);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s17, gas - 1)
      else
        ExecuteFromCFGNode_s219(s17, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 168
    * Starting at 0x146c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1566

    requires s0.stack[13] == 0x24c

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1566;
      assert s1.Peek(14) == 0x24c;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 220
    * Segment Id for this node is: 169
    * Starting at 0x1470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1566

    requires s0.stack[13] == 0x24c

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1566;
      assert s1.Peek(13) == 0x24c;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x1566;
      assert s11.Peek(15) == 0x24c;
      assert s11.Peek(16) == 0x20d;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1566;
      assert s21.Peek(11) == 0x24c;
      assert s21.Peek(12) == 0x20d;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s28, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 191
    * Starting at 0x1566
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1566 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x24c

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x24c;
      assert s1.Peek(7) == 0x20d;
      var s2 := Swap6(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Swap5(s3);
      var s5 := Swap1(s4);
      var s6 := Swap5(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Swap5(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x24c;
      assert s11.Peek(5) == 0x20d;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s14, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 57
    * Starting at 0x24c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x24c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x0597);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s3, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 91
    * Starting at 0x597
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x597 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x05d5);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x031c);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x31c;
      assert s11.Peek(4) == 0x5d5;
      assert s11.Peek(7) == 0x20d;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s224(s21, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 76
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x5d5

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5d5;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x5d5;
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x1094);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s21, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 143
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x5d5

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5d5;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x5d5;
      assert s11.Peek(9) == 0x20d;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x5d5;
      assert s21.Peek(7) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x5d5;
      assert s31.Peek(12) == 0x20d;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1108);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s227(s41, gas - 1)
      else
        ExecuteFromCFGNode_s226(s41, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 144
    * Starting at 0x10ff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x5d5

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x5d5;
      assert s1.Peek(10) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 227
    * Segment Id for this node is: 145
    * Starting at 0x1108
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1108 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x5d5

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x5d5;
      assert s1.Peek(9) == 0x20d;
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
      assert s11.Peek(6) == 0x5d5;
      assert s11.Peek(9) == 0x20d;
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
      assert s21.Peek(5) == 0x5d5;
      assert s21.Peek(8) == 0x20d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1644);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s28, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 209
    * Starting at 0x1644
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x5d5

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x5d5;
      assert s1.Peek(8) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1656);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s230(s10, gas - 1)
      else
        ExecuteFromCFGNode_s229(s10, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 210
    * Starting at 0x1652
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x5d5

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x5d5;
      assert s1.Peek(10) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 230
    * Segment Id for this node is: 211
    * Starting at 0x1656
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1656 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x5d5

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x5d5;
      assert s1.Peek(9) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x14cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s231(s7, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 176
    * Starting at 0x14cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x5d5

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x5d5;
      assert s1.Peek(12) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s8, gas - 1)
      else
        ExecuteFromCFGNode_s232(s8, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 177
    * Starting at 0x14d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x5d5

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x5d5;
      assert s1.Peek(13) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 233
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x5d5

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x5d5;
      assert s1.Peek(12) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s3, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x5d5

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x5d5;
      assert s1.Peek(10) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s7, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x5d5

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5d5;
      assert s1.Peek(6) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s6, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 92
    * Starting at 0x5d5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x06d2);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s4, gas - 1)
      else
        ExecuteFromCFGNode_s237(s4, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 93
    * Starting at 0x5db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x062f);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x62f;
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push32(s17, 0x726f636b657444414f50726f746f636f6c50726f706f73616c73000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x62f;
      assert s21.Peek(5) == 0x20d;
      var s22 := Push2(s21, 0x112c);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s238(s23, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 146
    * Starting at 0x112c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x62f

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x62f;
      assert s1.Peek(5) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1143);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x02e1);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2e1;
      assert s11.Peek(3) == 0x1143;
      assert s11.Peek(7) == 0x62f;
      assert s11.Peek(11) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x1661);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s239(s14, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 212
    * Starting at 0x1661
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1661 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x2e1

    requires s0.stack[3] == 0x1143

    requires s0.stack[7] == 0x62f

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2e1;
      assert s1.Peek(3) == 0x1143;
      assert s1.Peek(7) == 0x62f;
      assert s1.Peek(11) == 0x20d;
      var s2 := Push32(s1, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x163d);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x163d;
      assert s11.Peek(7) == 0x2e1;
      assert s11.Peek(8) == 0x1143;
      assert s11.Peek(12) == 0x62f;
      assert s11.Peek(16) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s12, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x163d

    requires s0.stack[6] == 0x2e1

    requires s0.stack[7] == 0x1143

    requires s0.stack[11] == 0x62f

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(6) == 0x2e1;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s241(s5, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0x62f

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x163d;
      assert s1.Peek(9) == 0x2e1;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0x62f;
      assert s1.Peek(18) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s243(s7, gas - 1)
      else
        ExecuteFromCFGNode_s242(s7, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0x62f

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x163d;
      assert s1.Peek(10) == 0x2e1;
      assert s1.Peek(11) == 0x1143;
      assert s1.Peek(15) == 0x62f;
      assert s1.Peek(19) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x163d;
      assert s11.Peek(10) == 0x2e1;
      assert s11.Peek(11) == 0x1143;
      assert s11.Peek(15) == 0x62f;
      assert s11.Peek(19) == 0x20d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s14, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0x62f

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x163d;
      assert s1.Peek(9) == 0x2e1;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0x62f;
      assert s1.Peek(18) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x163d;
      assert s11.Peek(6) == 0x2e1;
      assert s11.Peek(7) == 0x1143;
      assert s11.Peek(11) == 0x62f;
      assert s11.Peek(15) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s14, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x2e1

    requires s0.stack[5] == 0x1143

    requires s0.stack[9] == 0x62f

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2e1;
      assert s1.Peek(5) == 0x1143;
      assert s1.Peek(9) == 0x62f;
      assert s1.Peek(13) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s7, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 73
    * Starting at 0x2e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1143

    requires s0.stack[5] == 0x62f

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1143;
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x1143;
      assert s11.Peek(6) == 0x62f;
      assert s11.Peek(10) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0ffc);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s246(s21, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 140
    * Starting at 0xffc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1143

    requires s0.stack[5] == 0x62f

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1143;
      assert s1.Peek(5) == 0x62f;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x1143;
      assert s11.Peek(10) == 0x62f;
      assert s11.Peek(14) == 0x20d;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x1143;
      assert s21.Peek(8) == 0x62f;
      assert s21.Peek(12) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x1143;
      assert s31.Peek(13) == 0x62f;
      assert s31.Peek(17) == 0x20d;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1070);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s41, gas - 1)
      else
        ExecuteFromCFGNode_s247(s41, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 141
    * Starting at 0x1067
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x62f

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 248
    * Segment Id for this node is: 142
    * Starting at 0x1070
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x62f

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1143;
      assert s1.Peek(10) == 0x62f;
      assert s1.Peek(14) == 0x20d;
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
      assert s11.Peek(6) == 0x1143;
      assert s11.Peek(10) == 0x62f;
      assert s11.Peek(14) == 0x20d;
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
      assert s21.Peek(5) == 0x1143;
      assert s21.Peek(9) == 0x62f;
      assert s21.Peek(13) == 0x20d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1620);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s28, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 205
    * Starting at 0x1620
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x1143

    requires s0.stack[9] == 0x62f

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x1143;
      assert s1.Peek(9) == 0x62f;
      assert s1.Peek(13) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1632);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s251(s10, gas - 1)
      else
        ExecuteFromCFGNode_s250(s10, gas - 1)
  }

  /** Node 250
    * Segment Id for this node is: 206
    * Starting at 0x162e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x62f

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 251
    * Segment Id for this node is: 207
    * Starting at 0x1632
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x62f

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x1143;
      assert s1.Peek(10) == 0x62f;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1575);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s7, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 192
    * Starting at 0x1575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0x62f

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1143;
      assert s1.Peek(13) == 0x62f;
      assert s1.Peek(17) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s254(s8, gas - 1)
      else
        ExecuteFromCFGNode_s253(s8, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 193
    * Starting at 0x1593
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0x62f

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0x62f;
      assert s1.Peek(18) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 254
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0x62f

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1143;
      assert s1.Peek(13) == 0x62f;
      assert s1.Peek(17) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s255(s3, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x1143

    requires s0.stack[11] == 0x62f

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x62f;
      assert s1.Peek(15) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s7, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1143

    requires s0.stack[7] == 0x62f

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1143;
      assert s1.Peek(7) == 0x62f;
      assert s1.Peek(11) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s257(s6, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 147
    * Starting at 0x1143
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x62f

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(8) == 0x20d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x02fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s260(s8, gas - 1)
      else
        ExecuteFromCFGNode_s258(s8, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 148
    * Starting at 0x1161
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1161 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x62f

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(8) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x12);
      assert s11.Peek(5) == 0x62f;
      assert s11.Peek(9) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x62f;
      assert s21.Peek(9) == 0x20d;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x04d6);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s24, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 85
    * Starting at 0x4d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x62f

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x62f;
      assert s1.Peek(8) == 0x20d;
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

  /** Node 260
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x62f

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x62f;
      assert s1.Peek(7) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s6, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 94
    * Starting at 0x62f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x62f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x06d2);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s6, gas - 1)
      else
        ExecuteFromCFGNode_s262(s6, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 95
    * Starting at 0x64b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x39);
      assert s11.Peek(4) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f6e6c792044414f2050726f746f636f6c2050726f706f73616c7320636f6e74);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x726163742063616e2075706461746520612073657474696e6700000000000000);
      assert s21.Peek(4) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s126(s29, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 96
    * Starting at 0x6d2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := Add(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Swap2(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(4) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Swap2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x1b);
      assert s21.Peek(6) == 0x20d;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Push32(s23, 0x6e6574776f726b2e636f6e73656e7375732e7468726573686f6c640000000000);
      var s25 := Swap3(s24);
      var s26 := Add(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap2(s28);
      var s30 := MStore(s29);
      var s31 := Push32(s30, 0xc8e1147164b1f21d6af1808639b3ce87587dece56df325d691ea0a109e012957);
      assert s31.Peek(4) == 0x20d;
      var s32 := Dup2(s31);
      var s33 := Add(s32);
      var s34 := Push2(s33, 0x07d6);
      var s35 := JumpI(s34);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s34.stack[1] > 0 then
        ExecuteFromCFGNode_s283(s35, gas - 1)
      else
        ExecuteFromCFGNode_s264(s35, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 97
    * Starting at 0x73a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x73a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push8(s0, 0x0713e24c43730000);
      assert s1.Peek(4) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x07d1);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s6, gas - 1)
      else
        ExecuteFromCFGNode_s265(s6, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 98
    * Starting at 0x74a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x29);
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e73656e737573207468726573686f6c64206d7573742062652035312520);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x6f72206869676865720000000000000000000000000000000000000000000000);
      assert s21.Peek(5) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s29, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 85
    * Starting at 0x4d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
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

  /** Node 267
    * Segment Id for this node is: 99
    * Starting at 0x7d1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push2(s1, 0x0ba3);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s268(s3, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 118
    * Starting at 0xba3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push2(s1, 0x0bd7);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0bbb);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0xbbb;
      assert s11.Peek(4) == 0xbd7;
      assert s11.Peek(8) == 0x20d;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x160e);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s269(s15, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xbbb

    requires s0.stack[4] == 0xbd7

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xbbb;
      assert s1.Peek(4) == 0xbd7;
      assert s1.Peek(8) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0xbbb;
      assert s11.Peek(9) == 0xbd7;
      assert s11.Peek(13) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s270(s12, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0xbbb

    requires s0.stack[8] == 0xbd7

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0xbbb;
      assert s1.Peek(8) == 0xbd7;
      assert s1.Peek(12) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s271(s5, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xbbb

    requires s0.stack[11] == 0xbd7

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xbbb;
      assert s1.Peek(11) == 0xbd7;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s273(s7, gas - 1)
      else
        ExecuteFromCFGNode_s272(s7, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xbbb

    requires s0.stack[11] == 0xbd7

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0xbbb;
      assert s1.Peek(12) == 0xbd7;
      assert s1.Peek(16) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0xbbb;
      assert s11.Peek(12) == 0xbd7;
      assert s11.Peek(16) == 0x20d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s14, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0xbbb

    requires s0.stack[11] == 0xbd7

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0xbbb;
      assert s1.Peek(11) == 0xbd7;
      assert s1.Peek(15) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0xbbb;
      assert s11.Peek(8) == 0xbd7;
      assert s11.Peek(12) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s14, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[5] == 0xbbb

    requires s0.stack[6] == 0xbd7

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xbbb;
      assert s1.Peek(6) == 0xbd7;
      assert s1.Peek(10) == 0x20d;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s8, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 119
    * Starting at 0xbbb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbbb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xbd7

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xbd7;
      assert s1.Peek(5) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0xbd7;
      assert s11.Peek(6) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup4(s19);
      var s21 := Push2(s20, 0x1257);
      assert s21.Peek(0) == 0x1257;
      assert s21.Peek(3) == 0xbd7;
      assert s21.Peek(7) == 0x20d;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s276(s22, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 155
    * Starting at 0x1257
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1257 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xbd7

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xbd7;
      assert s1.Peek(6) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xe2a4853a00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0xbd7;
      assert s11.Peek(9) == 0x20d;
      var s12 := Dup5(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x24);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Dup4(s17);
      var s19 := Swap1(s18);
      var s20 := MStore(s19);
      var s21 := Push2(s20, 0x0100);
      assert s21.Peek(5) == 0xbd7;
      assert s21.Peek(9) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Swap2(s22);
      var s24 := Div(s23);
      var s25 := Push20(s24, 0xffffffffffffffffffffffffffffffffffffffff);
      var s26 := And(s25);
      var s27 := Swap1(s26);
      var s28 := Push4(s27, 0xe2a4853a);
      var s29 := Swap1(s28);
      var s30 := Push1(s29, 0x44);
      var s31 := Add(s30);
      assert s31.Peek(5) == 0xbd7;
      assert s31.Peek(9) == 0x20d;
      var s32 := Push2(s31, 0x1221);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s33, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 150
    * Starting at 0x1221
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1221 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0xbd7

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xbd7;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup8(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(12) == 0xbd7;
      assert s11.Peek(16) == 0x20d;
      var s12 := ExtCodeSize(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x123b);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s279(s17, gas - 1)
      else
        ExecuteFromCFGNode_s278(s17, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 151
    * Starting at 0x1237
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1237 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[12] == 0xbd7

    requires s0.stack[16] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0xbd7;
      assert s1.Peek(17) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 279
    * Segment Id for this node is: 152
    * Starting at 0x123b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x123b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[12] == 0xbd7

    requires s0.stack[16] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0xbd7;
      assert s1.Peek(16) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x124f);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s9, gas - 1)
      else
        ExecuteFromCFGNode_s280(s9, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 153
    * Starting at 0x1246
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1246 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0xbd7

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xbd7;
      assert s1.Peek(11) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 281
    * Segment Id for this node is: 154
    * Starting at 0x124f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x124f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0xbd7

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xbd7;
      assert s1.Peek(10) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s8, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 120
    * Starting at 0xbd7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s5, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 100
    * Starting at 0x7d6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x18);
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push32(s13, 0x6e6574776f726b2e6e6f64652e6665652e6d696e696d756d0000000000000000);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Swap2(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Push32(s19, 0x93ef100e2c4b7616b3e6782e01966d6fb06252033b2d58870662904feeb51066);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x20d;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x08dd);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s288(s24, gas - 1)
      else
        ExecuteFromCFGNode_s284(s24, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 101
    * Starting at 0x833
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x833 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 7, 0xb1a2bc2ec50000);
      assert s1.Peek(4) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0851);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s286(s8, gas - 1)
      else
        ExecuteFromCFGNode_s285(s8, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 102
    * Starting at 0x844
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x844 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push8(s1, 0x02c68af0bb140000);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s286(s5, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 103
    * Starting at 0x851
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x851 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push2(s1, 0x07d1);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s3, gas - 1)
      else
        ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 104
    * Starting at 0x856
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x856 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x37);
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x546865206e6f646520666565206d696e696d756d206d75737420626520612076);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x616c7565206265747765656e20352520616e6420323025000000000000000000);
      assert s21.Peek(5) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s29, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 105
    * Starting at 0x8dd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x17);
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push32(s13, 0x6e6574776f726b2e6e6f64652e6665652e746172676574000000000000000000);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Swap2(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Push32(s19, 0xfb2c7533e326ea2eddab96ed8c5e0f8bd7542a1ccfb98641addab2f2a84d34a1);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x20d;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x09e4);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s293(s24, gas - 1)
      else
        ExecuteFromCFGNode_s289(s24, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 106
    * Starting at 0x93a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 7, 0xb1a2bc2ec50000);
      assert s1.Peek(4) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0958);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s291(s8, gas - 1)
      else
        ExecuteFromCFGNode_s290(s8, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 107
    * Starting at 0x94b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push8(s1, 0x02c68af0bb140000);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s291(s5, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 108
    * Starting at 0x958
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x958 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push2(s1, 0x07d1);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s3, gas - 1)
      else
        ExecuteFromCFGNode_s292(s3, gas - 1)
  }

  /** Node 292
    * Segment Id for this node is: 109
    * Starting at 0x95d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x95d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x36);
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x546865206e6f64652066656520746172676574206d7573742062652061207661);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x6c7565206265747765656e20352520616e642032302500000000000000000000);
      assert s21.Peek(5) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s29, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 110
    * Starting at 0x9e4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9e4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Swap1(s7);
      var s9 := Swap2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x18);
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push32(s13, 0x6e6574776f726b2e6e6f64652e6665652e6d6178696d756d0000000000000000);
      var s15 := Push1(s14, 0x20);
      var s16 := Swap1(s15);
      var s17 := Swap2(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Push32(s19, 0xf3875d78e8082aacb2106592d0dd9b48f9271e22aee9f12295198b2e7ffe6cd3);
      var s21 := Dup2(s20);
      assert s21.Peek(5) == 0x20d;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x0aeb);
      var s24 := JumpI(s23);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s23.stack[1] > 0 then
        ExecuteFromCFGNode_s298(s24, gas - 1)
      else
        ExecuteFromCFGNode_s294(s24, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 111
    * Starting at 0xa41
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa41 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := PushN(s0, 7, 0xb1a2bc2ec50000);
      assert s1.Peek(4) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Dup1(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0a5f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s296(s8, gas - 1)
      else
        ExecuteFromCFGNode_s295(s8, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 112
    * Starting at 0xa52
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa52 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push8(s1, 0x02c68af0bb140000);
      var s3 := Dup3(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s296(s5, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 113
    * Starting at 0xa5f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push2(s1, 0x07d1);
      var s3 := JumpI(s2);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s2.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s3, gas - 1)
      else
        ExecuteFromCFGNode_s297(s3, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 114
    * Starting at 0xa64
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa64 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x37);
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x546865206e6f646520666565206d6178696d756d206d75737420626520612076);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x616c7565206265747765656e20352520616e6420323025000000000000000000);
      assert s21.Peek(5) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s29, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 115
    * Starting at 0xaeb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xaeb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0x60);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MStore(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x21);
      var s11 := Dup2(s10);
      assert s11.Peek(7) == 0x20d;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x16ad);
      var s16 := Push1(s15, 0x21);
      var s17 := Swap2(s16);
      var s18 := CodeCopy(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x20d;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Keccak256(s23);
      var s25 := Dup2(s24);
      var s26 := Sub(s25);
      var s27 := Push2(s26, 0x0ba3);
      var s28 := JumpI(s27);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s27.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s28, gas - 1)
      else
        ExecuteFromCFGNode_s299(s28, gas - 1)
  }

  /** Node 299
    * Segment Id for this node is: 116
    * Starting at 0xb12
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb12 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0e10);
      assert s1.Peek(4) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Lt(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x0ba3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s6, gas - 1)
      else
        ExecuteFromCFGNode_s300(s6, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 117
    * Starting at 0xb1c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb1c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x20d;
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
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x546865207375626d6974206672657175656e6379206d757374206265203e3d20);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x3120686f75720000000000000000000000000000000000000000000000000000);
      assert s21.Peek(5) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      var s28 := Push2(s27, 0x04d6);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s29, gas - 1)
  }

  /** Node 301
    * Segment Id for this node is: 55
    * Starting at 0x236
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x236 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0557);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s302(s4, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 90
    * Starting at 0x557
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x557 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x19);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e70656e616c74792e7468726573686f6c6400000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 303
    * Segment Id for this node is: 28
    * Starting at 0x114
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x114 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x31607418);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x020f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s309(s6, gas - 1)
      else
        ExecuteFromCFGNode_s304(s6, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 29
    * Starting at 0x120
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x54fd4d50);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0217);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s306(s5, gas - 1)
      else
        ExecuteFromCFGNode_s305(s5, gas - 1)
  }

  /** Node 305
    * Segment Id for this node is: 30
    * Starting at 0x12b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12b as nat
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

  /** Node 306
    * Segment Id for this node is: 53
    * Starting at 0x217
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x217 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push2(s3, 0x0224);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0xff);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s9, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 54
    * Starting at 0x224
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x224 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x224

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x224;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := Swap1(s4);
      var s6 := Swap2(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(1) == 0x224;
      var s12 := Push2(s11, 0x01b0);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s13, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 42
    * Starting at 0x1b0
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x224

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x224;
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

  /** Node 309
    * Segment Id for this node is: 52
    * Starting at 0x20f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0517);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s310(s4, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 89
    * Starting at 0x517
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x517 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e7375626d69742e7072696365732e6672657175656e637900);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 31
    * Starting at 0x12f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x1d5e50ea);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x0160);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s392(s6, gas - 1)
      else
        ExecuteFromCFGNode_s312(s6, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 32
    * Starting at 0x13b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1d5e50ea);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01dc);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s390(s5, gas - 1)
      else
        ExecuteFromCFGNode_s313(s5, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 33
    * Starting at 0x146
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1f66e8ed);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01f2);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s388(s5, gas - 1)
      else
        ExecuteFromCFGNode_s314(s5, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 34
    * Starting at 0x151
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x2a57d018);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01fa);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s316(s5, gas - 1)
      else
        ExecuteFromCFGNode_s315(s5, gas - 1)
  }

  /** Node 315
    * Segment Id for this node is: 35
    * Starting at 0x15c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15c as nat
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

  /** Node 316
    * Segment Id for this node is: 49
    * Starting at 0x1fa
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x020d);
      var s3 := Push2(s2, 0x0208);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x14de);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s317(s7, gas - 1)
  }

  /** Node 317
    * Segment Id for this node is: 179
    * Starting at 0x14de
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x208

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(3) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x14f1);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s319(s11, gas - 1)
      else
        ExecuteFromCFGNode_s318(s11, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 180
    * Starting at 0x14ed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14ed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x208

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x208;
      assert s1.Peek(6) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 319
    * Segment Id for this node is: 181
    * Starting at 0x14f1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x208

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x208;
      assert s1.Peek(5) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1508);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s321(s9, gas - 1)
      else
        ExecuteFromCFGNode_s320(s9, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 182
    * Starting at 0x1504
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1504 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x208

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x208;
      assert s1.Peek(7) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 321
    * Segment Id for this node is: 183
    * Starting at 0x1508
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1508 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x208

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x208;
      assert s1.Peek(6) == 0x20d;
      var s2 := Push2(s1, 0x1514);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x13e5);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s322(s8, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 161
    * Starting at 0x13e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x1514

    requires s0.stack[8] == 0x208

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1514;
      assert s1.Peek(8) == 0x208;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x13f6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s324(s9, gas - 1)
      else
        ExecuteFromCFGNode_s323(s9, gas - 1)
  }

  /** Node 323
    * Segment Id for this node is: 162
    * Starting at 0x13f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1514

    requires s0.stack[9] == 0x208

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1514;
      assert s1.Peek(10) == 0x208;
      assert s1.Peek(11) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 324
    * Segment Id for this node is: 163
    * Starting at 0x13f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x1514

    requires s0.stack[9] == 0x208

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1514;
      assert s1.Peek(9) == 0x208;
      assert s1.Peek(10) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1411);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s327(s10, gas - 1)
      else
        ExecuteFromCFGNode_s325(s10, gas - 1)
  }

  /** Node 325
    * Segment Id for this node is: 164
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1514

    requires s0.stack[11] == 0x208

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1411);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x1514;
      assert s1.Peek(12) == 0x208;
      assert s1.Peek(13) == 0x20d;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s326(s3, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[0] == 0x1411

    requires s0.stack[6] == 0x1514

    requires s0.stack[12] == 0x208

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x1514;
      assert s1.Peek(12) == 0x208;
      assert s1.Peek(13) == 0x20d;
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

  /** Node 327
    * Segment Id for this node is: 165
    * Starting at 0x1411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x1514

    requires s0.stack[11] == 0x208

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1514;
      assert s1.Peek(11) == 0x208;
      assert s1.Peek(12) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x1514;
      assert s11.Peek(15) == 0x208;
      assert s11.Peek(16) == 0x20d;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x1514;
      assert s21.Peek(16) == 0x208;
      assert s21.Peek(17) == 0x20d;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x1457);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s330(s26, gas - 1)
      else
        ExecuteFromCFGNode_s328(s26, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 166
    * Starting at 0x1450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1514

    requires s0.stack[13] == 0x208

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1457);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x1514;
      assert s1.Peek(14) == 0x208;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s329(s3, gas - 1)
  }

  /** Node 329
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[0] == 0x1457

    requires s0.stack[8] == 0x1514

    requires s0.stack[14] == 0x208

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x1514;
      assert s1.Peek(14) == 0x208;
      assert s1.Peek(15) == 0x20d;
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

  /** Node 330
    * Segment Id for this node is: 167
    * Starting at 0x1457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1514

    requires s0.stack[13] == 0x208

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1514;
      assert s1.Peek(13) == 0x208;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x1514;
      assert s11.Peek(17) == 0x208;
      assert s11.Peek(18) == 0x20d;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x1470);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s332(s17, gas - 1)
      else
        ExecuteFromCFGNode_s331(s17, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 168
    * Starting at 0x146c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1514

    requires s0.stack[13] == 0x208

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x1514;
      assert s1.Peek(14) == 0x208;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 332
    * Segment Id for this node is: 169
    * Starting at 0x1470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x1514

    requires s0.stack[13] == 0x208

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x1514;
      assert s1.Peek(13) == 0x208;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x1514;
      assert s11.Peek(15) == 0x208;
      assert s11.Peek(16) == 0x20d;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x1514;
      assert s21.Peek(11) == 0x208;
      assert s21.Peek(12) == 0x20d;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s333(s28, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 184
    * Starting at 0x1514
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1514 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x208

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x208;
      assert s1.Peek(7) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push2(s8, 0x1525);
      var s10 := Dup2(s9);
      var s11 := Push2(s10, 0x14cd);
      assert s11.Peek(0) == 0x14cd;
      assert s11.Peek(2) == 0x1525;
      assert s11.Peek(8) == 0x208;
      assert s11.Peek(9) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s334(s12, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 176
    * Starting at 0x14cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1525

    requires s0.stack[7] == 0x208

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1525;
      assert s1.Peek(7) == 0x208;
      assert s1.Peek(8) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s336(s8, gas - 1)
      else
        ExecuteFromCFGNode_s335(s8, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 177
    * Starting at 0x14d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1525

    requires s0.stack[7] == 0x208

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x1525;
      assert s1.Peek(8) == 0x208;
      assert s1.Peek(9) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 336
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x1525

    requires s0.stack[7] == 0x208

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1525;
      assert s1.Peek(7) == 0x208;
      assert s1.Peek(8) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s337(s3, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 185
    * Starting at 0x1525
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1525 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x208

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x208;
      assert s1.Peek(6) == 0x20d;
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
      ExecuteFromCFGNode_s338(s11, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 50
    * Starting at 0x208
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x208 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x039f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s339(s3, gas - 1)
  }

  /** Node 339
    * Segment Id for this node is: 80
    * Starting at 0x39f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x03dd);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Push2(s8, 0x031c);
      var s10 := Swap2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(3) == 0x31c;
      assert s11.Peek(4) == 0x3dd;
      assert s11.Peek(7) == 0x20d;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x28);
      var s19 := Add(s18);
      var s20 := Swap1(s19);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s340(s21, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 76
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x3dd

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3dd;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x3dd;
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x1094);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s341(s21, gas - 1)
  }

  /** Node 341
    * Segment Id for this node is: 143
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x3dd

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3dd;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x3dd;
      assert s11.Peek(9) == 0x20d;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x3dd;
      assert s21.Peek(7) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x3dd;
      assert s31.Peek(12) == 0x20d;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1108);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s41, gas - 1)
      else
        ExecuteFromCFGNode_s342(s41, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 144
    * Starting at 0x10ff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x3dd

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(10) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 343
    * Segment Id for this node is: 145
    * Starting at 0x1108
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1108 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x3dd

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x3dd;
      assert s1.Peek(9) == 0x20d;
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
      assert s11.Peek(6) == 0x3dd;
      assert s11.Peek(9) == 0x20d;
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
      assert s21.Peek(5) == 0x3dd;
      assert s21.Peek(8) == 0x20d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1644);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s28, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 209
    * Starting at 0x1644
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x3dd

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x3dd;
      assert s1.Peek(8) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1656);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s10, gas - 1)
      else
        ExecuteFromCFGNode_s345(s10, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 210
    * Starting at 0x1652
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x3dd

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(10) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 346
    * Segment Id for this node is: 211
    * Starting at 0x1656
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1656 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x3dd

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x3dd;
      assert s1.Peek(9) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x14cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s7, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 176
    * Starting at 0x14cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(12) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s349(s8, gas - 1)
      else
        ExecuteFromCFGNode_s348(s8, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 177
    * Starting at 0x14d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x3dd;
      assert s1.Peek(13) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 349
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s349(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x3dd

    requires s0.stack[12] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x3dd;
      assert s1.Peek(12) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s350(s3, gas - 1)
  }

  /** Node 350
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s350(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x3dd

    requires s0.stack[10] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x3dd;
      assert s1.Peek(10) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s351(s7, gas - 1)
  }

  /** Node 351
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s351(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x3dd

    requires s0.stack[6] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3dd;
      assert s1.Peek(6) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s352(s6, gas - 1)
  }

  /** Node 352
    * Segment Id for this node is: 81
    * Starting at 0x3dd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s352(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x04df);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s4, gas - 1)
      else
        ExecuteFromCFGNode_s353(s4, gas - 1)
  }

  /** Node 353
    * Segment Id for this node is: 82
    * Starting at 0x3e3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s353(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0437);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x437;
      assert s11.Peek(5) == 0x20d;
      var s12 := Dup1(s11);
      var s13 := Push1(s12, 0x1a);
      var s14 := Dup2(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Push32(s17, 0x726f636b657444414f50726f746f636f6c50726f706f73616c73000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(1) == 0x437;
      assert s21.Peek(5) == 0x20d;
      var s22 := Push2(s21, 0x112c);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s354(s23, gas - 1)
  }

  /** Node 354
    * Segment Id for this node is: 146
    * Starting at 0x112c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s354(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x437

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x437;
      assert s1.Peek(5) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1143);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x02e1);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x2e1;
      assert s11.Peek(3) == 0x1143;
      assert s11.Peek(7) == 0x437;
      assert s11.Peek(11) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x1661);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s355(s14, gas - 1)
  }

  /** Node 355
    * Segment Id for this node is: 212
    * Starting at 0x1661
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s355(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1661 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x2e1

    requires s0.stack[3] == 0x1143

    requires s0.stack[7] == 0x437

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2e1;
      assert s1.Peek(3) == 0x1143;
      assert s1.Peek(7) == 0x437;
      assert s1.Peek(11) == 0x20d;
      var s2 := Push32(s1, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x163d);
      var s7 := Push1(s6, 0x10);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x163d;
      assert s11.Peek(7) == 0x2e1;
      assert s11.Peek(8) == 0x1143;
      assert s11.Peek(12) == 0x437;
      assert s11.Peek(16) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s356(s12, gas - 1)
  }

  /** Node 356
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s356(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x163d

    requires s0.stack[6] == 0x2e1

    requires s0.stack[7] == 0x1143

    requires s0.stack[11] == 0x437

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(6) == 0x2e1;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x437;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s357(s5, gas - 1)
  }

  /** Node 357
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s357(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0x437

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x163d;
      assert s1.Peek(9) == 0x2e1;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0x437;
      assert s1.Peek(18) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s359(s7, gas - 1)
      else
        ExecuteFromCFGNode_s358(s7, gas - 1)
  }

  /** Node 358
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s358(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0x437

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x163d;
      assert s1.Peek(10) == 0x2e1;
      assert s1.Peek(11) == 0x1143;
      assert s1.Peek(15) == 0x437;
      assert s1.Peek(19) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x163d;
      assert s11.Peek(10) == 0x2e1;
      assert s11.Peek(11) == 0x1143;
      assert s11.Peek(15) == 0x437;
      assert s11.Peek(19) == 0x20d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s357(s14, gas - 1)
  }

  /** Node 359
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s359(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x163d

    requires s0.stack[9] == 0x2e1

    requires s0.stack[10] == 0x1143

    requires s0.stack[14] == 0x437

    requires s0.stack[18] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x163d;
      assert s1.Peek(9) == 0x2e1;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0x437;
      assert s1.Peek(18) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x163d;
      assert s11.Peek(6) == 0x2e1;
      assert s11.Peek(7) == 0x1143;
      assert s11.Peek(11) == 0x437;
      assert s11.Peek(15) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s360(s14, gas - 1)
  }

  /** Node 360
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s360(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x2e1

    requires s0.stack[5] == 0x1143

    requires s0.stack[9] == 0x437

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2e1;
      assert s1.Peek(5) == 0x1143;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(13) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s361(s7, gas - 1)
  }

  /** Node 361
    * Segment Id for this node is: 73
    * Starting at 0x2e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s361(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1143

    requires s0.stack[5] == 0x437

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1143;
      assert s1.Peek(5) == 0x437;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x1143;
      assert s11.Peek(6) == 0x437;
      assert s11.Peek(10) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0ffc);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s362(s21, gas - 1)
  }

  /** Node 362
    * Segment Id for this node is: 140
    * Starting at 0xffc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s362(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1143

    requires s0.stack[5] == 0x437

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1143;
      assert s1.Peek(5) == 0x437;
      assert s1.Peek(9) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x1143;
      assert s11.Peek(10) == 0x437;
      assert s11.Peek(14) == 0x20d;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x1143;
      assert s21.Peek(8) == 0x437;
      assert s21.Peek(12) == 0x20d;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x1143;
      assert s31.Peek(13) == 0x437;
      assert s31.Peek(17) == 0x20d;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1070);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s364(s41, gas - 1)
      else
        ExecuteFromCFGNode_s363(s41, gas - 1)
  }

  /** Node 363
    * Segment Id for this node is: 141
    * Starting at 0x1067
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s363(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x437

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x437;
      assert s1.Peek(15) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 364
    * Segment Id for this node is: 142
    * Starting at 0x1070
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s364(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x437

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1143;
      assert s1.Peek(10) == 0x437;
      assert s1.Peek(14) == 0x20d;
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
      assert s11.Peek(6) == 0x1143;
      assert s11.Peek(10) == 0x437;
      assert s11.Peek(14) == 0x20d;
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
      assert s21.Peek(5) == 0x1143;
      assert s21.Peek(9) == 0x437;
      assert s21.Peek(13) == 0x20d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1620);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s365(s28, gas - 1)
  }

  /** Node 365
    * Segment Id for this node is: 205
    * Starting at 0x1620
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s365(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x1143

    requires s0.stack[9] == 0x437

    requires s0.stack[13] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x1143;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(13) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1632);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s367(s10, gas - 1)
      else
        ExecuteFromCFGNode_s366(s10, gas - 1)
  }

  /** Node 366
    * Segment Id for this node is: 206
    * Starting at 0x162e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s366(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x437

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x437;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 367
    * Segment Id for this node is: 207
    * Starting at 0x1632
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s367(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1143

    requires s0.stack[10] == 0x437

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x1143;
      assert s1.Peek(10) == 0x437;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1575);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s368(s7, gas - 1)
  }

  /** Node 368
    * Segment Id for this node is: 192
    * Starting at 0x1575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s368(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0x437

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1143;
      assert s1.Peek(13) == 0x437;
      assert s1.Peek(17) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s370(s8, gas - 1)
      else
        ExecuteFromCFGNode_s369(s8, gas - 1)
  }

  /** Node 369
    * Segment Id for this node is: 193
    * Starting at 0x1593
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s369(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0x437

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1143;
      assert s1.Peek(14) == 0x437;
      assert s1.Peek(18) == 0x20d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 370
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s370(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1143

    requires s0.stack[13] == 0x437

    requires s0.stack[17] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1143;
      assert s1.Peek(13) == 0x437;
      assert s1.Peek(17) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s371(s3, gas - 1)
  }

  /** Node 371
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s371(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x1143

    requires s0.stack[11] == 0x437

    requires s0.stack[15] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1143;
      assert s1.Peek(11) == 0x437;
      assert s1.Peek(15) == 0x20d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s372(s7, gas - 1)
  }

  /** Node 372
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s372(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1143

    requires s0.stack[7] == 0x437

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1143;
      assert s1.Peek(7) == 0x437;
      assert s1.Peek(11) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s373(s6, gas - 1)
  }

  /** Node 373
    * Segment Id for this node is: 147
    * Starting at 0x1143
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s373(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1143 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x437

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x437;
      assert s1.Peek(8) == 0x20d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x02fc);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s376(s8, gas - 1)
      else
        ExecuteFromCFGNode_s374(s8, gas - 1)
  }

  /** Node 374
    * Segment Id for this node is: 148
    * Starting at 0x1161
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s374(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1161 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x437

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x437;
      assert s1.Peek(8) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x12);
      assert s11.Peek(5) == 0x437;
      assert s11.Peek(9) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x64);
      assert s21.Peek(5) == 0x437;
      assert s21.Peek(9) == 0x20d;
      var s22 := Add(s21);
      var s23 := Push2(s22, 0x04d6);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s375(s24, gas - 1)
  }

  /** Node 375
    * Segment Id for this node is: 85
    * Starting at 0x4d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s375(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x437

    requires s0.stack[8] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x437;
      assert s1.Peek(8) == 0x20d;
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

  /** Node 376
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s376(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x437

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x437;
      assert s1.Peek(7) == 0x20d;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s377(s6, gas - 1)
  }

  /** Node 377
    * Segment Id for this node is: 83
    * Starting at 0x437
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s377(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x437 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x20d;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x04df);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s379(s6, gas - 1)
      else
        ExecuteFromCFGNode_s378(s6, gas - 1)
  }

  /** Node 378
    * Segment Id for this node is: 84
    * Starting at 0x453
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s378(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x453 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x20d;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Push1(s6, 0x04);
      var s8 := Dup3(s7);
      var s9 := Add(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x39);
      assert s11.Peek(4) == 0x20d;
      var s12 := Push1(s11, 0x24);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push32(s15, 0x4f6e6c792044414f2050726f746f636f6c2050726f706f73616c7320636f6e74);
      var s17 := Push1(s16, 0x44);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := MStore(s19);
      var s21 := Push32(s20, 0x726163742063616e2075706461746520612073657474696e6700000000000000);
      assert s21.Peek(4) == 0x20d;
      var s22 := Push1(s21, 0x64);
      var s23 := Dup3(s22);
      var s24 := Add(s23);
      var s25 := MStore(s24);
      var s26 := Push1(s25, 0x84);
      var s27 := Add(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s126(s27, gas - 1)
  }

  /** Node 379
    * Segment Id for this node is: 86
    * Starting at 0x4df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s379(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x20d;
      var s2 := Push2(s1, 0x0513);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x04f7);
      var s11 := Swap3(s10);
      assert s11.Peek(3) == 0x4f7;
      assert s11.Peek(4) == 0x513;
      assert s11.Peek(7) == 0x20d;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Push2(s13, 0x160e);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s380(s15, gas - 1)
  }

  /** Node 380
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s380(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x4f7

    requires s0.stack[4] == 0x513

    requires s0.stack[7] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4f7;
      assert s1.Peek(4) == 0x513;
      assert s1.Peek(7) == 0x20d;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0x4f7;
      assert s11.Peek(9) == 0x513;
      assert s11.Peek(12) == 0x20d;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s381(s12, gas - 1)
  }

  /** Node 381
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s381(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x4f7

    requires s0.stack[8] == 0x513

    requires s0.stack[11] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x4f7;
      assert s1.Peek(8) == 0x513;
      assert s1.Peek(11) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s382(s5, gas - 1)
  }

  /** Node 382
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s382(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x4f7

    requires s0.stack[11] == 0x513

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x4f7;
      assert s1.Peek(11) == 0x513;
      assert s1.Peek(14) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s384(s7, gas - 1)
      else
        ExecuteFromCFGNode_s383(s7, gas - 1)
  }

  /** Node 383
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s383(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x4f7

    requires s0.stack[11] == 0x513

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x4f7;
      assert s1.Peek(12) == 0x513;
      assert s1.Peek(15) == 0x20d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0x4f7;
      assert s11.Peek(12) == 0x513;
      assert s11.Peek(15) == 0x20d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s382(s14, gas - 1)
  }

  /** Node 384
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s384(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x4f7

    requires s0.stack[11] == 0x513

    requires s0.stack[14] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x4f7;
      assert s1.Peek(11) == 0x513;
      assert s1.Peek(14) == 0x20d;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0x4f7;
      assert s11.Peek(8) == 0x513;
      assert s11.Peek(11) == 0x20d;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s385(s14, gas - 1)
  }

  /** Node 385
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s385(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x4f7

    requires s0.stack[6] == 0x513

    requires s0.stack[9] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x4f7;
      assert s1.Peek(6) == 0x513;
      assert s1.Peek(9) == 0x20d;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s386(s8, gas - 1)
  }

  /** Node 386
    * Segment Id for this node is: 87
    * Starting at 0x4f7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s386(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x513

    requires s0.stack[4] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x513;
      assert s1.Peek(4) == 0x20d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x513;
      assert s11.Peek(5) == 0x20d;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Dup3(s19);
      var s21 := Push2(s20, 0x11c2);
      assert s21.Peek(0) == 0x11c2;
      assert s21.Peek(3) == 0x513;
      assert s21.Peek(6) == 0x20d;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s387(s22, gas - 1)
  }

  /** Node 387
    * Segment Id for this node is: 149
    * Starting at 0x11c2
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s387(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x513

    requires s0.stack[5] == 0x20d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x513;
      assert s1.Peek(5) == 0x20d;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Push32(s5, 0xabfdcced00000000000000000000000000000000000000000000000000000000);
      var s7 := Dup2(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x04);
      var s10 := Dup2(s9);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x513;
      assert s11.Peek(8) == 0x20d;
      var s12 := Dup5(s11);
      var s13 := Swap1(s12);
      var s14 := MStore(s13);
      var s15 := Dup3(s14);
      var s16 := IsZero(s15);
      var s17 := IsZero(s16);
      var s18 := Push1(s17, 0x24);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0x513;
      assert s21.Peek(7) == 0x20d;
      var s22 := Push2(s21, 0x0100);
      var s23 := Swap1(s22);
      var s24 := Swap2(s23);
      var s25 := Div(s24);
      var s26 := Push20(s25, 0xffffffffffffffffffffffffffffffffffffffff);
      var s27 := And(s26);
      var s28 := Swap1(s27);
      var s29 := Push4(s28, 0xabfdcced);
      var s30 := Swap1(s29);
      var s31 := Push1(s30, 0x44);
      assert s31.Peek(6) == 0x513;
      assert s31.Peek(9) == 0x20d;
      var s32 := Add(s31);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s136(s32, gas - 1)
  }

  /** Node 388
    * Segment Id for this node is: 48
    * Starting at 0x1f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s388(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x035f);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s389(s4, gas - 1)
  }

  /** Node 389
    * Segment Id for this node is: 79
    * Starting at 0x35f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s389(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x1b);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6574776f726b2e636f6e73656e7375732e7468726573686f6c640000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 390
    * Segment Id for this node is: 46
    * Starting at 0x1dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s390(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01e4);
      var s3 := Push2(s2, 0x0337);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s391(s4, gas - 1)
  }

  /** Node 391
    * Segment Id for this node is: 77
    * Starting at 0x337
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s391(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x337 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x1e4

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1e4;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x035a);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x35a;
      assert s11.Peek(4) == 0x1e4;
      var s12 := Push1(s11, 0x21);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x16ad);
      var s18 := Push1(s17, 0x21);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push2(s20, 0x0d18);
      assert s21.Peek(0) == 0xd18;
      assert s21.Peek(2) == 0x35a;
      assert s21.Peek(4) == 0x1e4;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s22, gas - 1)
  }

  /** Node 392
    * Segment Id for this node is: 36
    * Starting at 0x160
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s392(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x1386a244);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x017c);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s434(s6, gas - 1)
      else
        ExecuteFromCFGNode_s393(s6, gas - 1)
  }

  /** Node 393
    * Segment Id for this node is: 37
    * Starting at 0x16c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s393(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1bfcc24e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01b9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s395(s5, gas - 1)
      else
        ExecuteFromCFGNode_s394(s5, gas - 1)
  }

  /** Node 394
    * Segment Id for this node is: 38
    * Starting at 0x177
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s394(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
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

  /** Node 395
    * Segment Id for this node is: 43
    * Starting at 0x1b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s395(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01cc);
      var s3 := Push2(s2, 0x01c7);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1490);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s396(s7, gas - 1)
  }

  /** Node 396
    * Segment Id for this node is: 170
    * Starting at 0x1490
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s396(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1490 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x1c7

    requires s0.stack[3] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c7;
      assert s1.Peek(3) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x14a2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s398(s10, gas - 1)
      else
        ExecuteFromCFGNode_s397(s10, gas - 1)
  }

  /** Node 397
    * Segment Id for this node is: 171
    * Starting at 0x149e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s397(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1c7

    requires s0.stack[4] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1c7;
      assert s1.Peek(5) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 398
    * Segment Id for this node is: 172
    * Starting at 0x14a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s398(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x1c7

    requires s0.stack[4] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c7;
      assert s1.Peek(4) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s400(s9, gas - 1)
      else
        ExecuteFromCFGNode_s399(s9, gas - 1)
  }

  /** Node 399
    * Segment Id for this node is: 173
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s399(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c7

    requires s0.stack[5] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1c7;
      assert s1.Peek(6) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 400
    * Segment Id for this node is: 174
    * Starting at 0x14b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s400(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x1c7

    requires s0.stack[5] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c7;
      assert s1.Peek(5) == 0x1cc;
      var s2 := Push2(s1, 0x14c5);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x13e5);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s401(s8, gas - 1)
  }

  /** Node 401
    * Segment Id for this node is: 161
    * Starting at 0x13e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s401(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x1c7

    requires s0.stack[8] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x1c7;
      assert s1.Peek(8) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x13f6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s403(s9, gas - 1)
      else
        ExecuteFromCFGNode_s402(s9, gas - 1)
  }

  /** Node 402
    * Segment Id for this node is: 162
    * Starting at 0x13f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s402(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x14c5

    requires s0.stack[8] == 0x1c7

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x14c5;
      assert s1.Peek(9) == 0x1c7;
      assert s1.Peek(10) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 403
    * Segment Id for this node is: 163
    * Starting at 0x13f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s403(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x14c5

    requires s0.stack[8] == 0x1c7

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x14c5;
      assert s1.Peek(8) == 0x1c7;
      assert s1.Peek(9) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1411);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s406(s10, gas - 1)
      else
        ExecuteFromCFGNode_s404(s10, gas - 1)
  }

  /** Node 404
    * Segment Id for this node is: 164
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s404(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x1c7

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1411);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x1c7;
      assert s1.Peek(12) == 0x1cc;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s405(s3, gas - 1)
  }

  /** Node 405
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s405(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1411

    requires s0.stack[6] == 0x14c5

    requires s0.stack[11] == 0x1c7

    requires s0.stack[12] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x1c7;
      assert s1.Peek(12) == 0x1cc;
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

  /** Node 406
    * Segment Id for this node is: 165
    * Starting at 0x1411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s406(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x1c7

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x1c7;
      assert s1.Peek(11) == 0x1cc;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x14c5;
      assert s11.Peek(14) == 0x1c7;
      assert s11.Peek(15) == 0x1cc;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x14c5;
      assert s21.Peek(15) == 0x1c7;
      assert s21.Peek(16) == 0x1cc;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x1457);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s409(s26, gas - 1)
      else
        ExecuteFromCFGNode_s407(s26, gas - 1)
  }

  /** Node 407
    * Segment Id for this node is: 166
    * Starting at 0x1450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s407(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x1c7

    requires s0.stack[13] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1457);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x1c7;
      assert s1.Peek(14) == 0x1cc;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s408(s3, gas - 1)
  }

  /** Node 408
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s408(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x1457

    requires s0.stack[8] == 0x14c5

    requires s0.stack[13] == 0x1c7

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x1c7;
      assert s1.Peek(14) == 0x1cc;
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

  /** Node 409
    * Segment Id for this node is: 167
    * Starting at 0x1457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s409(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x1c7

    requires s0.stack[13] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x14c5;
      assert s1.Peek(12) == 0x1c7;
      assert s1.Peek(13) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x14c5;
      assert s11.Peek(16) == 0x1c7;
      assert s11.Peek(17) == 0x1cc;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x1470);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s411(s17, gas - 1)
      else
        ExecuteFromCFGNode_s410(s17, gas - 1)
  }

  /** Node 410
    * Segment Id for this node is: 168
    * Starting at 0x146c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s410(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x1c7

    requires s0.stack[13] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x1c7;
      assert s1.Peek(14) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 411
    * Segment Id for this node is: 169
    * Starting at 0x1470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s411(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x1c7

    requires s0.stack[13] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x14c5;
      assert s1.Peek(12) == 0x1c7;
      assert s1.Peek(13) == 0x1cc;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x14c5;
      assert s11.Peek(14) == 0x1c7;
      assert s11.Peek(15) == 0x1cc;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x14c5;
      assert s21.Peek(10) == 0x1c7;
      assert s21.Peek(11) == 0x1cc;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s412(s28, gas - 1)
  }

  /** Node 412
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s412(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x1c7

    requires s0.stack[6] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1c7;
      assert s1.Peek(6) == 0x1cc;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s413(s8, gas - 1)
  }

  /** Node 413
    * Segment Id for this node is: 44
    * Starting at 0x1c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s413(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1cc;
      var s2 := Push2(s1, 0x0302);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s414(s3, gas - 1)
  }

  /** Node 414
    * Segment Id for this node is: 75
    * Starting at 0x302
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s414(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x302 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02fc);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x031c);
      assert s11.Peek(0) == 0x31c;
      assert s11.Peek(4) == 0x2fc;
      assert s11.Peek(7) == 0x1cc;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x160e);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s415(s16, gas - 1)
  }

  /** Node 415
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s415(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x31c

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x31c;
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x1cc;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0x31c;
      assert s11.Peek(9) == 0x2fc;
      assert s11.Peek(12) == 0x1cc;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s416(s12, gas - 1)
  }

  /** Node 416
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s416(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x31c

    requires s0.stack[8] == 0x2fc

    requires s0.stack[11] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x31c;
      assert s1.Peek(8) == 0x2fc;
      assert s1.Peek(11) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s417(s5, gas - 1)
  }

  /** Node 417
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s417(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x31c

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x31c;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s419(s7, gas - 1)
      else
        ExecuteFromCFGNode_s418(s7, gas - 1)
  }

  /** Node 418
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s418(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x31c

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x31c;
      assert s1.Peek(12) == 0x2fc;
      assert s1.Peek(15) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0x31c;
      assert s11.Peek(12) == 0x2fc;
      assert s11.Peek(15) == 0x1cc;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s417(s14, gas - 1)
  }

  /** Node 419
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s419(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x31c

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x31c;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x1cc;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0x31c;
      assert s11.Peek(8) == 0x2fc;
      assert s11.Peek(11) == 0x1cc;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s420(s14, gas - 1)
  }

  /** Node 420
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s420(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x31c

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x31c;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1cc;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s421(s8, gas - 1)
  }

  /** Node 421
    * Segment Id for this node is: 76
    * Starting at 0x31c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s421(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x1cc;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x2fc;
      assert s11.Peek(5) == 0x1cc;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x1094);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s422(s21, gas - 1)
  }

  /** Node 422
    * Segment Id for this node is: 143
    * Starting at 0x1094
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s422(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1094 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x7ae1cfca00000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x1cc;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x2fc;
      assert s21.Peek(7) == 0x1cc;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x7ae1cfca);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x2fc;
      assert s31.Peek(12) == 0x1cc;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1108);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s424(s41, gas - 1)
      else
        ExecuteFromCFGNode_s423(s41, gas - 1)
  }

  /** Node 423
    * Segment Id for this node is: 144
    * Starting at 0x10ff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s423(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 424
    * Segment Id for this node is: 145
    * Starting at 0x1108
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s424(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1108 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1cc;
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
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x1cc;
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
      assert s21.Peek(5) == 0x2fc;
      assert s21.Peek(8) == 0x1cc;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1644);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s425(s28, gas - 1)
  }

  /** Node 425
    * Segment Id for this node is: 209
    * Starting at 0x1644
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s425(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1644 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x2fc

    requires s0.stack[8] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x2fc;
      assert s1.Peek(8) == 0x1cc;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1656);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s427(s10, gas - 1)
      else
        ExecuteFromCFGNode_s426(s10, gas - 1)
  }

  /** Node 426
    * Segment Id for this node is: 210
    * Starting at 0x1652
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s426(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1652 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 427
    * Segment Id for this node is: 211
    * Starting at 0x1656
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s427(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1656 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x1cc;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x14cd);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s428(s7, gas - 1)
  }

  /** Node 428
    * Segment Id for this node is: 176
    * Starting at 0x14cd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s428(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x2fc;
      assert s1.Peek(12) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := IsZero(s2);
      var s4 := IsZero(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s430(s8, gas - 1)
      else
        ExecuteFromCFGNode_s429(s8, gas - 1)
  }

  /** Node 429
    * Segment Id for this node is: 177
    * Starting at 0x14d7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s429(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x2fc;
      assert s1.Peek(13) == 0x1cc;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 430
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s430(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x2fc;
      assert s1.Peek(12) == 0x1cc;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s431(s3, gas - 1)
  }

  /** Node 431
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s431(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x2fc

    requires s0.stack[10] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x1cc;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s432(s7, gas - 1)
  }

  /** Node 432
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s432(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x1cc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s433(s6, gas - 1)
  }

  /** Node 433
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s433(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1cc

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1cc;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s6, gas - 1)
  }

  /** Node 434
    * Segment Id for this node is: 39
    * Starting at 0x17c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s434(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x17c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x018f);
      var s3 := Push2(s2, 0x018a);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x1490);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s435(s7, gas - 1)
  }

  /** Node 435
    * Segment Id for this node is: 170
    * Starting at 0x1490
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s435(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1490 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x18a

    requires s0.stack[3] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x18a;
      assert s1.Peek(3) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x14a2);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s437(s10, gas - 1)
      else
        ExecuteFromCFGNode_s436(s10, gas - 1)
  }

  /** Node 436
    * Segment Id for this node is: 171
    * Starting at 0x149e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s436(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x149e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x18a

    requires s0.stack[4] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x18a;
      assert s1.Peek(5) == 0x18f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 437
    * Segment Id for this node is: 172
    * Starting at 0x14a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s437(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x18a

    requires s0.stack[4] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x18a;
      assert s1.Peek(4) == 0x18f;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x14b9);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s439(s9, gas - 1)
      else
        ExecuteFromCFGNode_s438(s9, gas - 1)
  }

  /** Node 438
    * Segment Id for this node is: 173
    * Starting at 0x14b5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s438(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x18a

    requires s0.stack[5] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x18a;
      assert s1.Peek(6) == 0x18f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 439
    * Segment Id for this node is: 174
    * Starting at 0x14b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s439(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x18a

    requires s0.stack[5] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x18a;
      assert s1.Peek(5) == 0x18f;
      var s2 := Push2(s1, 0x14c5);
      var s3 := Dup5(s2);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x13e5);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s440(s8, gas - 1)
  }

  /** Node 440
    * Segment Id for this node is: 161
    * Starting at 0x13e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s440(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x18a

    requires s0.stack[8] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x18a;
      assert s1.Peek(8) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x13f6);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s442(s9, gas - 1)
      else
        ExecuteFromCFGNode_s441(s9, gas - 1)
  }

  /** Node 441
    * Segment Id for this node is: 162
    * Starting at 0x13f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s441(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x14c5

    requires s0.stack[8] == 0x18a

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x14c5;
      assert s1.Peek(9) == 0x18a;
      assert s1.Peek(10) == 0x18f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 442
    * Segment Id for this node is: 163
    * Starting at 0x13f6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s442(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x14c5

    requires s0.stack[8] == 0x18a

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x14c5;
      assert s1.Peek(8) == 0x18a;
      assert s1.Peek(9) == 0x18f;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1411);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s445(s10, gas - 1)
      else
        ExecuteFromCFGNode_s443(s10, gas - 1)
  }

  /** Node 443
    * Segment Id for this node is: 164
    * Starting at 0x140a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s443(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x140a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x18a

    requires s0.stack[11] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1411);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x18a;
      assert s1.Peek(12) == 0x18f;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s444(s3, gas - 1)
  }

  /** Node 444
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s444(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[0] == 0x1411

    requires s0.stack[6] == 0x14c5

    requires s0.stack[11] == 0x18a

    requires s0.stack[12] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1411;
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x18a;
      assert s1.Peek(12) == 0x18f;
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

  /** Node 445
    * Segment Id for this node is: 165
    * Starting at 0x1411
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s445(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1411 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x18a

    requires s0.stack[11] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x18a;
      assert s1.Peek(11) == 0x18f;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push32(s6, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x3f);
      assert s11.Peek(9) == 0x14c5;
      assert s11.Peek(14) == 0x18a;
      assert s11.Peek(15) == 0x18f;
      var s12 := Add(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Add(s14);
      var s16 := Swap1(s15);
      var s17 := Dup3(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := Dup2(s19);
      var s21 := Dup4(s20);
      assert s21.Peek(10) == 0x14c5;
      assert s21.Peek(15) == 0x18a;
      assert s21.Peek(16) == 0x18f;
      var s22 := Lt(s21);
      var s23 := Or(s22);
      var s24 := IsZero(s23);
      var s25 := Push2(s24, 0x1457);
      var s26 := JumpI(s25);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s25.stack[1] > 0 then
        ExecuteFromCFGNode_s448(s26, gas - 1)
      else
        ExecuteFromCFGNode_s446(s26, gas - 1)
  }

  /** Node 446
    * Segment Id for this node is: 166
    * Starting at 0x1450
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s446(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1450 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x18a

    requires s0.stack[13] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x1457);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x18a;
      assert s1.Peek(14) == 0x18f;
      var s2 := Push2(s1, 0x13b6);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s447(s3, gas - 1)
  }

  /** Node 447
    * Segment Id for this node is: 160
    * Starting at 0x13b6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s447(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13b6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x1457

    requires s0.stack[8] == 0x14c5

    requires s0.stack[13] == 0x18a

    requires s0.stack[14] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1457;
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x18a;
      assert s1.Peek(14) == 0x18f;
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

  /** Node 448
    * Segment Id for this node is: 167
    * Starting at 0x1457
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s448(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x18a

    requires s0.stack[13] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x14c5;
      assert s1.Peek(12) == 0x18a;
      assert s1.Peek(13) == 0x18f;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Dup4(s4);
      var s6 := Dup2(s5);
      var s7 := MStore(s6);
      var s8 := Dup7(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup6(s9);
      var s11 := Dup9(s10);
      assert s11.Peek(11) == 0x14c5;
      assert s11.Peek(16) == 0x18a;
      assert s11.Peek(17) == 0x18f;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x1470);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s450(s17, gas - 1)
      else
        ExecuteFromCFGNode_s449(s17, gas - 1)
  }

  /** Node 449
    * Segment Id for this node is: 168
    * Starting at 0x146c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s449(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x146c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x18a

    requires s0.stack[13] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x14c5;
      assert s1.Peek(13) == 0x18a;
      assert s1.Peek(14) == 0x18f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 450
    * Segment Id for this node is: 169
    * Starting at 0x1470
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s450(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1470 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[7] == 0x14c5

    requires s0.stack[12] == 0x18a

    requires s0.stack[13] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x14c5;
      assert s1.Peek(12) == 0x18a;
      assert s1.Peek(13) == 0x18f;
      var s2 := Dup4(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup4(s6);
      var s8 := Add(s7);
      var s9 := CallDataCopy(s8);
      var s10 := Push1(s9, 0x00);
      var s11 := Push1(s10, 0x20);
      assert s11.Peek(9) == 0x14c5;
      assert s11.Peek(14) == 0x18a;
      assert s11.Peek(15) == 0x18f;
      var s12 := Dup6(s11);
      var s13 := Dup4(s12);
      var s14 := Add(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup1(s16);
      var s18 := Swap5(s17);
      var s19 := Pop(s18);
      var s20 := Pop(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x14c5;
      assert s21.Peek(10) == 0x18a;
      assert s21.Peek(11) == 0x18f;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s451(s28, gas - 1)
  }

  /** Node 451
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s451(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x18a

    requires s0.stack[6] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x18a;
      assert s1.Peek(6) == 0x18f;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s452(s8, gas - 1)
  }

  /** Node 452
    * Segment Id for this node is: 40
    * Starting at 0x18a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s452(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18f;
      var s2 := Push2(s1, 0x02c7);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s453(s3, gas - 1)
  }

  /** Node 453
    * Segment Id for this node is: 72
    * Starting at 0x2c7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s453(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x02fc);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x02e1);
      assert s11.Peek(0) == 0x2e1;
      assert s11.Peek(4) == 0x2fc;
      assert s11.Peek(7) == 0x18f;
      var s12 := Swap3(s11);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x160e);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s454(s16, gas - 1)
  }

  /** Node 454
    * Segment Id for this node is: 204
    * Starting at 0x160e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s454(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x2e1

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2e1;
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x18f;
      var s2 := Dup3(s1);
      var s3 := Dup2(s2);
      var s4 := MStore(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := Push2(s5, 0x14c5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := Dup5(s9);
      var s11 := Push2(s10, 0x15de);
      assert s11.Peek(0) == 0x15de;
      assert s11.Peek(3) == 0x14c5;
      assert s11.Peek(8) == 0x2e1;
      assert s11.Peek(9) == 0x2fc;
      assert s11.Peek(12) == 0x18f;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s455(s12, gas - 1)
  }

  /** Node 455
    * Segment Id for this node is: 200
    * Starting at 0x15de
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s455(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x14c5

    requires s0.stack[7] == 0x2e1

    requires s0.stack[8] == 0x2fc

    requires s0.stack[11] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x14c5;
      assert s1.Peek(7) == 0x2e1;
      assert s1.Peek(8) == 0x2fc;
      assert s1.Peek(11) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s456(s5, gas - 1)
  }

  /** Node 456
    * Segment Id for this node is: 201
    * Starting at 0x15e5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s456(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x2e1

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x2e1;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x18f;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x15ff);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s458(s7, gas - 1)
      else
        ExecuteFromCFGNode_s457(s7, gas - 1)
  }

  /** Node 457
    * Segment Id for this node is: 202
    * Starting at 0x15ee
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s457(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ee as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x2e1

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x14c5;
      assert s1.Peek(11) == 0x2e1;
      assert s1.Peek(12) == 0x2fc;
      assert s1.Peek(15) == 0x18f;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(6) == 0x14c5;
      assert s11.Peek(11) == 0x2e1;
      assert s11.Peek(12) == 0x2fc;
      assert s11.Peek(15) == 0x18f;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x15e5);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s456(s14, gas - 1)
  }

  /** Node 458
    * Segment Id for this node is: 203
    * Starting at 0x15ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s458(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[5] == 0x14c5

    requires s0.stack[10] == 0x2e1

    requires s0.stack[11] == 0x2fc

    requires s0.stack[14] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x14c5;
      assert s1.Peek(10) == 0x2e1;
      assert s1.Peek(11) == 0x2fc;
      assert s1.Peek(14) == 0x18f;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap4(s3);
      var s5 := Add(s4);
      var s6 := Swap3(s5);
      var s7 := Dup4(s6);
      var s8 := MStore(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(0) == 0x14c5;
      assert s11.Peek(7) == 0x2e1;
      assert s11.Peek(8) == 0x2fc;
      assert s11.Peek(11) == 0x18f;
      var s12 := Swap1(s11);
      var s13 := Pop(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s459(s14, gas - 1)
  }

  /** Node 459
    * Segment Id for this node is: 175
    * Starting at 0x14c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s459(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[5] == 0x2e1

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2e1;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x18f;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s460(s8, gas - 1)
  }

  /** Node 460
    * Segment Id for this node is: 73
    * Starting at 0x2e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s460(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x18f;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Sub(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(2) == 0x2fc;
      assert s11.Peek(5) == 0x18f;
      var s12 := Push1(s11, 0x40);
      var s13 := MStore(s12);
      var s14 := Dup1(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Keccak256(s18);
      var s20 := Push2(s19, 0x0ffc);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s461(s21, gas - 1)
  }

  /** Node 461
    * Segment Id for this node is: 140
    * Starting at 0xffc
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s461(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xffc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x2fc

    requires s0.stack[4] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2fc;
      assert s1.Peek(4) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push32(s6, 0x21f8a72100000000000000000000000000000000000000000000000000000000);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x18f;
      var s12 := Add(s11);
      var s13 := Dup5(s12);
      var s14 := Swap1(s13);
      var s15 := MStore(s14);
      var s16 := Push2(s15, 0x0100);
      var s17 := Swap1(s16);
      var s18 := Swap2(s17);
      var s19 := Div(s18);
      var s20 := Push20(s19, 0xffffffffffffffffffffffffffffffffffffffff);
      var s21 := And(s20);
      assert s21.Peek(4) == 0x2fc;
      assert s21.Peek(7) == 0x18f;
      var s22 := Swap1(s21);
      var s23 := Push4(s22, 0x21f8a721);
      var s24 := Swap1(s23);
      var s25 := Push1(s24, 0x24);
      var s26 := Add(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Push1(s27, 0x40);
      var s29 := MLoad(s28);
      var s30 := Dup1(s29);
      var s31 := Dup4(s30);
      assert s31.Peek(9) == 0x2fc;
      assert s31.Peek(12) == 0x18f;
      var s32 := Sub(s31);
      var s33 := Dup2(s32);
      var s34 := Dup7(s33);
      var s35 := Gas(s34);
      var s36 := StaticCall(s35);
      var s37 := IsZero(s36);
      var s38 := Dup1(s37);
      var s39 := IsZero(s38);
      var s40 := Push2(s39, 0x1070);
      var s41 := JumpI(s40);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s40.stack[1] > 0 then
        ExecuteFromCFGNode_s463(s41, gas - 1)
      else
        ExecuteFromCFGNode_s462(s41, gas - 1)
  }

  /** Node 462
    * Segment Id for this node is: 141
    * Starting at 0x1067
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s462(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1067 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 463
    * Segment Id for this node is: 142
    * Starting at 0x1070
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s463(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1070 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x18f;
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
      assert s11.Peek(6) == 0x2fc;
      assert s11.Peek(9) == 0x18f;
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
      assert s21.Peek(5) == 0x2fc;
      assert s21.Peek(8) == 0x18f;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x02fc);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x1620);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s464(s28, gas - 1)
  }

  /** Node 464
    * Segment Id for this node is: 205
    * Starting at 0x1620
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s464(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1620 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2fc

    requires s0.stack[5] == 0x2fc

    requires s0.stack[8] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2fc;
      assert s1.Peek(5) == 0x2fc;
      assert s1.Peek(8) == 0x18f;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x1632);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s466(s10, gas - 1)
      else
        ExecuteFromCFGNode_s465(s10, gas - 1)
  }

  /** Node 465
    * Segment Id for this node is: 206
    * Starting at 0x162e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s465(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x162e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x18f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 466
    * Segment Id for this node is: 207
    * Starting at 0x1632
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s466(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1632 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x18f;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x163d);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x1575);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s467(s7, gas - 1)
  }

  /** Node 467
    * Segment Id for this node is: 192
    * Starting at 0x1575
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s467(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1575 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x2fc;
      assert s1.Peek(12) == 0x18f;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := Dup2(s2);
      var s4 := And(s3);
      var s5 := Dup2(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x14db);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s469(s8, gas - 1)
      else
        ExecuteFromCFGNode_s468(s8, gas - 1)
  }

  /** Node 468
    * Segment Id for this node is: 193
    * Starting at 0x1593
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s468(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1593 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x163d;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x2fc;
      assert s1.Peek(13) == 0x18f;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 469
    * Segment Id for this node is: 178
    * Starting at 0x14db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s469(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x163d

    requires s0.stack[6] == 0x2fc

    requires s0.stack[9] == 0x2fc

    requires s0.stack[12] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x163d;
      assert s1.Peek(6) == 0x2fc;
      assert s1.Peek(9) == 0x2fc;
      assert s1.Peek(12) == 0x18f;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s470(s3, gas - 1)
  }

  /** Node 470
    * Segment Id for this node is: 208
    * Starting at 0x163d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s470(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x163d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x2fc

    requires s0.stack[7] == 0x2fc

    requires s0.stack[10] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x2fc;
      assert s1.Peek(7) == 0x2fc;
      assert s1.Peek(10) == 0x18f;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s471(s7, gas - 1)
  }

  /** Node 471
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s471(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x2fc

    requires s0.stack[6] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2fc;
      assert s1.Peek(6) == 0x18f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s472(s6, gas - 1)
  }

  /** Node 472
    * Segment Id for this node is: 74
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s472(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x18f

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x18f;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s473(s6, gas - 1)
  }

  /** Node 473
    * Segment Id for this node is: 41
    * Starting at 0x18f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s473(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Swap1(s4);
      var s6 := Swap2(s5);
      var s7 := And(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s11, gas - 1)
  }

  /** Node 474
    * Segment Id for this node is: 38
    * Starting at 0x177
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s474(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x177 as nat
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
