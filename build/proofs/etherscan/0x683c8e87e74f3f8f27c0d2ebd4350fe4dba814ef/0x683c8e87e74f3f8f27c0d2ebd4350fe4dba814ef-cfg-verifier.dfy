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
      assert s1.Peek(0) == 0x80;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x04);
      var s5 := CallDataSize(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x004e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s271(s8, gas - 1)
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
      var s6 := Push4(s5, 0x3659cfe6);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x0065);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s205(s9, gas - 1)
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
      var s2 := Push4(s1, 0x4f1ef286);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0085);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s113(s5, gas - 1)
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
      var s2 := Push4(s1, 0x5c60da1b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0098);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s5, gas - 1)
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
      var s2 := Push4(s1, 0x8f283970);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00c9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s5, gas - 1)
      else
        ExecuteFromCFGNode_s5(s5, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 5
    * Starting at 0x3f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
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
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0xf851a440);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x00e9);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s5, gas - 1)
      else
        ExecuteFromCFGNode_s6(s5, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 6
    * Starting at 0x4a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x005d);
      assert s1.Peek(0) == 0x5d;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s7(s2, gas - 1)
  }

  /** Node 7
    * Segment Id for this node is: 10
    * Starting at 0x5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x005b);
      var s3 := Push2(s2, 0x00fe);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s8(s4, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 28
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5b;
      var s2 := Push2(s1, 0x0106);
      var s3 := Push2(s2, 0x029b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s9(s4, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 58
    * Starting at 0x29b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x02a3);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s4, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x2a3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s11(s3, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x2a3

    requires s0.stack[3] == 0x106

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a3;
      assert s1.Peek(3) == 0x106;
      assert s1.Peek(4) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x2a3;
      assert s11.Peek(2) == 0x106;
      assert s11.Peek(3) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s12, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 59
    * Starting at 0x2a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x106;
      assert s11.Peek(6) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0116);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s18, gas - 1)
      else
        ExecuteFromCFGNode_s13(s18, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 60
    * Starting at 0x2bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
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
      assert s11.Peek(3) == 0x106;
      assert s11.Peek(4) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x42);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x106;
      assert s21.Peek(4) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push2(s27, 0x195d);
      var s29 := Push1(s28, 0xf2);
      var s30 := Shl(s29);
      var s31 := Push1(s30, 0x84);
      assert s31.Peek(3) == 0x106;
      assert s31.Peek(4) == 0x5b;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0xa4);
      var s36 := Add(s35);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s14(s36, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
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

  /** Node 15
    * Segment Id for this node is: 31
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x5b;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s2, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 29
    * Starting at 0x106
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5b;
      var s2 := Push2(s1, 0x0116);
      var s3 := Push2(s2, 0x0111);
      var s4 := Push2(s3, 0x033a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s5, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 62
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x111

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x111;
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01fb);
      var s4 := Push2(s3, 0x0492);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s5, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 82
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x038c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s5, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0x111;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0x111;
      assert s11.Peek(4) == 0x116;
      assert s11.Peek(5) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s12, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x5b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s5, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 30
    * Starting at 0x111
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push2(s1, 0x0344);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s22(s3, gas - 1)
  }

  /** Node 22
    * Segment Id for this node is: 63
    * Starting at 0x344
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x5b;
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
      assert s11.Peek(7) == 0x116;
      assert s11.Peek(8) == 0x5b;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0363);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s21, gas - 1)
      else
        ExecuteFromCFGNode_s23(s21, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 64
    * Starting at 0x35f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x116;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 24
    * Segment Id for this node is: 65
    * Starting at 0x363
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x363 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x5b;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 25
    * Segment Id for this node is: 25
    * Starting at 0xe9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe9 as nat
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
      var s5 := Push2(s4, 0x00f5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s27(s6, gas - 1)
      else
        ExecuteFromCFGNode_s26(s6, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 26
    * Starting at 0xf1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf1 as nat
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

  /** Node 27
    * Segment Id for this node is: 27
    * Starting at 0xf5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00ad);
      var s4 := Push2(s3, 0x0235);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s5, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 52
    * Starting at 0x235
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x235 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x023f);
      var s4 := Push2(s3, 0x0368);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s5, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x23f

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x23f;
      assert s1.Peek(2) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s30(s3, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x23f

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x23f;
      assert s1.Peek(4) == 0xad;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x23f;
      assert s11.Peek(3) == 0xad;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s12, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 53
    * Starting at 0x23f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xad;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(6) == 0xad;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0200);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s18, gas - 1)
      else
        ExecuteFromCFGNode_s32(s18, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 54
    * Starting at 0x259
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x259 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x01fb);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0xad;
      var s2 := Push2(s1, 0x0368);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s3, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s34(s3, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0xad;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0xad;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s12, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xad;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s5, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 20
    * Starting at 0xad
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad as nat
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
      var s16 := Push1(s15, 0x40);
      var s17 := MLoad(s16);
      var s18 := Dup1(s17);
      var s19 := Swap2(s18);
      var s20 := Sub(s19);
      var s21 := Swap1(s20);
      var s22 := Return(s21);
      // Segment is terminal (Revert, Stop or Return)
      s22
  }

  /** Node 37
    * Segment Id for this node is: 47
    * Starting at 0x200
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x200 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xad;
      var s2 := Push2(s1, 0x0208);
      var s3 := Push2(s2, 0x00fe);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s4, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 28
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x208

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x208;
      assert s1.Peek(2) == 0xad;
      var s2 := Push2(s1, 0x0106);
      var s3 := Push2(s2, 0x029b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s4, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 58
    * Starting at 0x29b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x208

    requires s0.stack[3] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x208;
      assert s1.Peek(3) == 0xad;
      var s2 := Push2(s1, 0x02a3);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s4, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x2a3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x208

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s41(s3, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x2a3

    requires s0.stack[3] == 0x106

    requires s0.stack[4] == 0x208

    requires s0.stack[6] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a3;
      assert s1.Peek(3) == 0x106;
      assert s1.Peek(4) == 0x208;
      assert s1.Peek(6) == 0xad;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x2a3;
      assert s11.Peek(2) == 0x106;
      assert s11.Peek(3) == 0x208;
      assert s11.Peek(5) == 0xad;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s12, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 59
    * Starting at 0x2a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x208

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x106;
      assert s11.Peek(6) == 0x208;
      assert s11.Peek(8) == 0xad;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0116);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s18, gas - 1)
      else
        ExecuteFromCFGNode_s43(s18, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 60
    * Starting at 0x2bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x208

    requires s0.stack[3] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
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
      assert s11.Peek(3) == 0x106;
      assert s11.Peek(4) == 0x208;
      assert s11.Peek(6) == 0xad;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x42);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x106;
      assert s21.Peek(4) == 0x208;
      assert s21.Peek(6) == 0xad;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push2(s27, 0x195d);
      var s29 := Push1(s28, 0xf2);
      var s30 := Shl(s29);
      var s31 := Push1(s30, 0x84);
      assert s31.Peek(3) == 0x106;
      assert s31.Peek(4) == 0x208;
      assert s31.Peek(6) == 0xad;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0xa4);
      var s36 := Add(s35);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s44(s36, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x208

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
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

  /** Node 45
    * Segment Id for this node is: 31
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x208

    requires s0.stack[3] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x208;
      assert s1.Peek(3) == 0xad;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s2, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 29
    * Starting at 0x106
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x208

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x208;
      assert s1.Peek(2) == 0xad;
      var s2 := Push2(s1, 0x0116);
      var s3 := Push2(s2, 0x0111);
      var s4 := Push2(s3, 0x033a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s5, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 62
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x111

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x208

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x111;
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01fb);
      var s4 := Push2(s3, 0x0492);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s48(s5, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 82
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x208

    requires s0.stack[6] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x208;
      assert s1.Peek(6) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x038c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s5, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x208

    requires s0.stack[8] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0x111;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x208;
      assert s1.Peek(8) == 0xad;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0x111;
      assert s11.Peek(4) == 0x116;
      assert s11.Peek(5) == 0x208;
      assert s11.Peek(7) == 0xad;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s12, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x208

    requires s0.stack[6] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x208;
      assert s1.Peek(6) == 0xad;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s5, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 30
    * Starting at 0x111
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x208

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
      var s2 := Push2(s1, 0x0344);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 63
    * Starting at 0x344
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x208

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x208;
      assert s1.Peek(4) == 0xad;
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
      assert s11.Peek(7) == 0x116;
      assert s11.Peek(8) == 0x208;
      assert s11.Peek(10) == 0xad;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0363);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s21, gas - 1)
      else
        ExecuteFromCFGNode_s53(s21, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 64
    * Starting at 0x35f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x208

    requires s0.stack[6] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x116;
      assert s1.Peek(5) == 0x208;
      assert s1.Peek(7) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 54
    * Segment Id for this node is: 65
    * Starting at 0x363
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x363 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x208

    requires s0.stack[6] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x208;
      assert s1.Peek(6) == 0xad;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 55
    * Segment Id for this node is: 21
    * Starting at 0xc9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc9 as nat
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
      var s5 := Push2(s4, 0x00d5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s57(s6, gas - 1)
      else
        ExecuteFromCFGNode_s56(s6, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 22
    * Starting at 0xd1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd1 as nat
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

  /** Node 57
    * Segment Id for this node is: 23
    * Starting at 0xd5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x005b);
      var s4 := Push2(s3, 0x00e4);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x06fb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s58(s8, gas - 1)
  }

  /** Node 58
    * Segment Id for this node is: 105
    * Starting at 0x6fb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0xe4

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xe4;
      assert s1.Peek(3) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x070d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s60(s10, gas - 1)
      else
        ExecuteFromCFGNode_s59(s10, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 106
    * Starting at 0x709
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x709 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xe4

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0xe4;
      assert s1.Peek(5) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 60
    * Segment Id for this node is: 107
    * Starting at 0x70d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0xe4

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe4;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push2(s1, 0x0285);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x06df);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s5, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 102
    * Starting at 0x6df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x285

    requires s0.stack[5] == 0xe4

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x285;
      assert s1.Peek(5) == 0xe4;
      assert s1.Peek(6) == 0x5b;
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
      assert s11.Peek(4) == 0x285;
      assert s11.Peek(8) == 0xe4;
      assert s11.Peek(9) == 0x5b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x06f6);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s14, gas - 1)
      else
        ExecuteFromCFGNode_s62(s14, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 103
    * Starting at 0x6f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x285

    requires s0.stack[6] == 0xe4

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x285;
      assert s1.Peek(7) == 0xe4;
      assert s1.Peek(8) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 63
    * Segment Id for this node is: 104
    * Starting at 0x6f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x285

    requires s0.stack[6] == 0xe4

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x285;
      assert s1.Peek(6) == 0xe4;
      assert s1.Peek(7) == 0x5b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s5, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 56
    * Starting at 0x285
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x285 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0xe4

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe4;
      assert s1.Peek(5) == 0x5b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s7, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 24
    * Starting at 0xe4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x020b);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s3, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 49
    * Starting at 0x20b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x0213);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s4, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x213

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x213;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s68(s3, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x213

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x213;
      assert s1.Peek(4) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x213;
      assert s11.Peek(3) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s12, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 50
    * Starting at 0x213
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(6) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0157);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s18, gas - 1)
      else
        ExecuteFromCFGNode_s70(s18, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 51
    * Starting at 0x22d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0154);
      assert s1.Peek(0) == 0x154;
      assert s1.Peek(2) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Push2(s2, 0x03c6);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s4, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 74
    * Starting at 0x3c6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154;
      assert s1.Peek(3) == 0x5b;
      var s2 := Push32(s1, 0x7e644d79422f17c01e4894b5f4f588d331ebfa28653d42ae832dc59e38c9798f);
      var s3 := Push2(s2, 0x03ef);
      var s4 := Push2(s3, 0x0368);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s72(s5, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x3ef

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3ef;
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x3ef

    requires s0.stack[5] == 0x154

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3ef;
      assert s1.Peek(5) == 0x154;
      assert s1.Peek(7) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x3ef;
      assert s11.Peek(4) == 0x154;
      assert s11.Peek(6) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s12, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 75
    * Starting at 0x3ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := Swap3(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(7) == 0x154;
      assert s11.Peek(9) == 0x5b;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Swap2(s14);
      var s16 := Dup5(s15);
      var s17 := And(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup4(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(4) == 0x154;
      assert s21.Peek(6) == 0x5b;
      var s22 := Add(s21);
      var s23 := Push1(s22, 0x40);
      var s24 := MLoad(s23);
      var s25 := Dup1(s24);
      var s26 := Swap2(s25);
      var s27 := Sub(s26);
      var s28 := Swap1(s27);
      var s29 := Log1(s28);
      var s30 := Push2(s29, 0x0154);
      var s31 := Dup2(s30);
      assert s31.Peek(1) == 0x154;
      assert s31.Peek(3) == 0x154;
      assert s31.Peek(5) == 0x5b;
      var s32 := Push2(s31, 0x04fa);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s33, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 85
    * Starting at 0x4fa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154;
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x055f);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s10, gas - 1)
      else
        ExecuteFromCFGNode_s76(s10, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 86
    * Starting at 0x509
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x509 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
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
      assert s11.Peek(4) == 0x154;
      assert s11.Peek(6) == 0x154;
      assert s11.Peek(8) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x26);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x455243313936373a206e65772061646d696e20697320746865207a65726f2061);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x154;
      assert s21.Peek(6) == 0x154;
      assert s21.Peek(8) == 0x5b;
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
      assert s31.Peek(2) == 0x154;
      assert s31.Peek(4) == 0x154;
      assert s31.Peek(6) == 0x5b;
      var s32 := Push2(s31, 0x0331);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s33, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
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

  /** Node 78
    * Segment Id for this node is: 87
    * Starting at 0x55f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154;
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s79(s3, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 88
    * Starting at 0x582
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x582 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x154

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x154;
      assert s1.Peek(7) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(5) == 0x154;
      assert s11.Peek(7) == 0x154;
      assert s11.Peek(9) == 0x5b;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Swap3(s15);
      var s17 := Swap1(s16);
      var s18 := Swap3(s17);
      var s19 := And(s18);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x154;
      assert s21.Peek(6) == 0x154;
      assert s21.Peek(8) == 0x5b;
      var s22 := Swap2(s21);
      var s23 := Or(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s27, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 35
    * Starting at 0x154
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x154;
      assert s1.Peek(3) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s3, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 35
    * Starting at 0x154
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s3, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 9
    * Starting at 0x5b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b as nat
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

  /** Node 83
    * Segment Id for this node is: 36
    * Starting at 0x157
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x0154);
      var s3 := Push2(s2, 0x00fe);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s4, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 28
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x154

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x154;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push2(s1, 0x0106);
      var s3 := Push2(s2, 0x029b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s85(s4, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 58
    * Starting at 0x29b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x154;
      assert s1.Peek(3) == 0x5b;
      var s2 := Push2(s1, 0x02a3);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s86(s4, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x2a3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s87(s3, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x2a3

    requires s0.stack[3] == 0x106

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a3;
      assert s1.Peek(3) == 0x106;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x2a3;
      assert s11.Peek(2) == 0x106;
      assert s11.Peek(3) == 0x154;
      assert s11.Peek(5) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s88(s12, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 59
    * Starting at 0x2a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x106;
      assert s11.Peek(6) == 0x154;
      assert s11.Peek(8) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0116);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s18, gas - 1)
      else
        ExecuteFromCFGNode_s89(s18, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 60
    * Starting at 0x2bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
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
      assert s11.Peek(3) == 0x106;
      assert s11.Peek(4) == 0x154;
      assert s11.Peek(6) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x42);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x106;
      assert s21.Peek(4) == 0x154;
      assert s21.Peek(6) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push2(s27, 0x195d);
      var s29 := Push1(s28, 0xf2);
      var s30 := Shl(s29);
      var s31 := Push1(s30, 0x84);
      assert s31.Peek(3) == 0x106;
      assert s31.Peek(4) == 0x154;
      assert s31.Peek(6) == 0x5b;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0xa4);
      var s36 := Add(s35);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s90(s36, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
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

  /** Node 91
    * Segment Id for this node is: 31
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x154

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x154;
      assert s1.Peek(3) == 0x5b;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s2, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 29
    * Starting at 0x106
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x154

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x154;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push2(s1, 0x0116);
      var s3 := Push2(s2, 0x0111);
      var s4 := Push2(s3, 0x033a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s93(s5, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 62
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x111

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x111;
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01fb);
      var s4 := Push2(s3, 0x0492);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s5, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 82
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x038c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s5, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x154

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0x111;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x154;
      assert s1.Peek(8) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0x111;
      assert s11.Peek(4) == 0x116;
      assert s11.Peek(5) == 0x154;
      assert s11.Peek(7) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s12, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s5, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 30
    * Starting at 0x111
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push2(s1, 0x0344);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s3, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 63
    * Starting at 0x344
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x154

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x154;
      assert s1.Peek(4) == 0x5b;
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
      assert s11.Peek(7) == 0x116;
      assert s11.Peek(8) == 0x154;
      assert s11.Peek(10) == 0x5b;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0363);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s21, gas - 1)
      else
        ExecuteFromCFGNode_s99(s21, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 64
    * Starting at 0x35f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x116;
      assert s1.Peek(5) == 0x154;
      assert s1.Peek(7) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 100
    * Segment Id for this node is: 65
    * Starting at 0x363
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x363 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 101
    * Segment Id for this node is: 17
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
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
      var s5 := Push2(s4, 0x00a4);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s103(s6, gas - 1)
      else
        ExecuteFromCFGNode_s102(s6, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 18
    * Starting at 0xa0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa0 as nat
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

  /** Node 103
    * Segment Id for this node is: 19
    * Starting at 0xa4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x00ad);
      var s4 := Push2(s3, 0x01d0);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s104(s5, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 43
    * Starting at 0x1d0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01da);
      var s4 := Push2(s3, 0x0368);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s5, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x1da

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1da;
      assert s1.Peek(2) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s106(s3, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x1da

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1da;
      assert s1.Peek(4) == 0xad;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1da;
      assert s11.Peek(3) == 0xad;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s12, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 44
    * Starting at 0x1da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xad;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(6) == 0xad;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0200);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s18, gas - 1)
      else
        ExecuteFromCFGNode_s108(s18, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 45
    * Starting at 0x1f4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x01fb);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0xad;
      var s2 := Push2(s1, 0x033a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s3, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 62
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01fb);
      var s4 := Push2(s3, 0x0492);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s110(s5, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 82
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0xad;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x038c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s111(s5, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0x1fb

    requires s0.stack[6] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0x1fb;
      assert s1.Peek(6) == 0xad;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0x1fb;
      assert s11.Peek(5) == 0xad;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s12, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0xad

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0xad;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s35(s5, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 15
    * Starting at 0x85
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x005b);
      var s3 := Push2(s2, 0x0093);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x0716);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s114(s7, gas - 1)
  }

  /** Node 114
    * Segment Id for this node is: 108
    * Starting at 0x716
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x716 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x93

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x93;
      assert s1.Peek(3) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup5(s5);
      var s7 := Dup7(s6);
      var s8 := Sub(s7);
      var s9 := SLt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x072b);
      assert s11.Peek(0) == 0x72b;
      assert s11.Peek(7) == 0x93;
      assert s11.Peek(8) == 0x5b;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s12, gas - 1)
      else
        ExecuteFromCFGNode_s115(s12, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 109
    * Starting at 0x727
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x727 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x93

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x93;
      assert s1.Peek(7) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 116
    * Segment Id for this node is: 110
    * Starting at 0x72b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x93

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x93;
      assert s1.Peek(6) == 0x5b;
      var s2 := Push2(s1, 0x0734);
      var s3 := Dup5(s2);
      var s4 := Push2(s3, 0x06df);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s5, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 102
    * Starting at 0x6df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[1] == 0x734

    requires s0.stack[7] == 0x93

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x734;
      assert s1.Peek(7) == 0x93;
      assert s1.Peek(8) == 0x5b;
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
      assert s11.Peek(4) == 0x734;
      assert s11.Peek(10) == 0x93;
      assert s11.Peek(11) == 0x5b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x06f6);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s14, gas - 1)
      else
        ExecuteFromCFGNode_s118(s14, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 103
    * Starting at 0x6f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x734

    requires s0.stack[8] == 0x93

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x734;
      assert s1.Peek(9) == 0x93;
      assert s1.Peek(10) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 119
    * Segment Id for this node is: 104
    * Starting at 0x6f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x734

    requires s0.stack[8] == 0x93

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x734;
      assert s1.Peek(8) == 0x93;
      assert s1.Peek(9) == 0x5b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s120(s5, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 111
    * Starting at 0x734
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x734 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x93

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x93;
      assert s1.Peek(7) == 0x5b;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push8(s7, 0xffffffffffffffff);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Gt(s10);
      assert s11.Peek(8) == 0x93;
      assert s11.Peek(9) == 0x5b;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0751);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s122(s14, gas - 1)
      else
        ExecuteFromCFGNode_s121(s14, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 112
    * Starting at 0x74d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x74d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x93

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x93;
      assert s1.Peek(9) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 122
    * Segment Id for this node is: 113
    * Starting at 0x751
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x751 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x93

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x93;
      assert s1.Peek(8) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Dup7(s2);
      var s4 := Add(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Dup7(s6);
      var s8 := Push1(s7, 0x1f);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := SLt(s10);
      assert s11.Peek(8) == 0x93;
      assert s11.Peek(9) == 0x5b;
      var s12 := Push2(s11, 0x0765);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s124(s13, gas - 1)
      else
        ExecuteFromCFGNode_s123(s13, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 114
    * Starting at 0x761
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x761 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x93

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x93;
      assert s1.Peek(9) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 124
    * Segment Id for this node is: 115
    * Starting at 0x765
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x765 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x93

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x93;
      assert s1.Peek(8) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Dup2(s4);
      var s6 := Gt(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0774);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s9, gas - 1)
      else
        ExecuteFromCFGNode_s125(s9, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 116
    * Starting at 0x770
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x770 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x93

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x93;
      assert s1.Peek(10) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 126
    * Segment Id for this node is: 117
    * Starting at 0x774
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x774 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x93

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x93;
      assert s1.Peek(9) == 0x5b;
      var s2 := Dup8(s1);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup6(s4);
      var s6 := Add(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0786);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s11, gas - 1)
      else
        ExecuteFromCFGNode_s127(s11, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 118
    * Starting at 0x782
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x782 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x93

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x93;
      assert s1.Peek(10) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 128
    * Segment Id for this node is: 119
    * Starting at 0x786
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x786 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x93

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x93;
      assert s1.Peek(9) == 0x5b;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := Swap5(s4);
      var s6 := Pop(s5);
      var s7 := Dup1(s6);
      var s8 := Swap4(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(6) == 0x93;
      assert s11.Peek(7) == 0x5b;
      var s12 := Pop(s11);
      var s13 := Swap3(s12);
      var s14 := Pop(s13);
      var s15 := Swap3(s14);
      var s16 := Pop(s15);
      var s17 := Swap3(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s129(s18, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 16
    * Starting at 0x93
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x93 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b;
      var s2 := Push2(s1, 0x015f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s130(s3, gas - 1)
  }

  /** Node 130
    * Segment Id for this node is: 37
    * Starting at 0x15f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x15f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b;
      var s2 := Push2(s1, 0x0167);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s4, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x167

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x167;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s132(s3, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x167

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x167;
      assert s1.Peek(6) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x167;
      assert s11.Peek(5) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s12, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 38
    * Starting at 0x167
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x167 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(8) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x01c8);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s18, gas - 1)
      else
        ExecuteFromCFGNode_s134(s18, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 39
    * Starting at 0x181
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 12
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x181 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x01c3);
      assert s1.Peek(0) == 0x1c3;
      assert s1.Peek(4) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Dup1(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup1(s9);
      var s11 := Swap2(s10);
      assert s11.Peek(7) == 0x1c3;
      assert s11.Peek(11) == 0x5b;
      var s12 := Div(s11);
      var s13 := Mul(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push1(s15, 0x40);
      var s17 := MLoad(s16);
      var s18 := Swap1(s17);
      var s19 := Dup2(s18);
      var s20 := Add(s19);
      var s21 := Push1(s20, 0x40);
      assert s21.Peek(7) == 0x1c3;
      assert s21.Peek(11) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Dup1(s22);
      var s24 := Swap4(s23);
      var s25 := Swap3(s24);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Dup2(s27);
      var s29 := Dup2(s28);
      var s30 := MStore(s29);
      var s31 := Push1(s30, 0x20);
      assert s31.Peek(7) == 0x1c3;
      assert s31.Peek(11) == 0x5b;
      var s32 := Add(s31);
      var s33 := Dup4(s32);
      var s34 := Dup4(s33);
      var s35 := Dup1(s34);
      var s36 := Dup3(s35);
      var s37 := Dup5(s36);
      var s38 := CallDataCopy(s37);
      var s39 := Push1(s38, 0x00);
      var s40 := Swap3(s39);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s135(s41, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 40
    * Starting at 0x1b3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[8] == 0x1c3

    requires s0.stack[12] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap2(s0);
      assert s1.Peek(8) == 0x1c3;
      assert s1.Peek(12) == 0x5b;
      var s2 := Swap1(s1);
      var s3 := Swap2(s2);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Swap3(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x039b);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x39b;
      assert s11.Peek(5) == 0x1c3;
      assert s11.Peek(9) == 0x5b;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s136(s13, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 68
    * Starting at 0x39b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1c3

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c3;
      assert s1.Peek(7) == 0x5b;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x04ba);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s137(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 83
    * Starting at 0x4ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3a4

    requires s0.stack[5] == 0x1c3

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a4;
      assert s1.Peek(5) == 0x1c3;
      assert s1.Peek(9) == 0x5b;
      var s2 := Push2(s1, 0x04c3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0621);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s5, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 96
    * Starting at 0x621
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x621 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x4c3

    requires s0.stack[3] == 0x3a4

    requires s0.stack[7] == 0x1c3

    requires s0.stack[11] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c3;
      assert s1.Peek(3) == 0x3a4;
      assert s1.Peek(7) == 0x1c3;
      assert s1.Peek(11) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := ExtCodeSize(s8);
      var s10 := Push2(s9, 0x068e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s11, gas - 1)
      else
        ExecuteFromCFGNode_s139(s11, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 97
    * Starting at 0x631
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x631 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x4c3

    requires s0.stack[3] == 0x3a4

    requires s0.stack[7] == 0x1c3

    requires s0.stack[11] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x4c3;
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(8) == 0x1c3;
      assert s1.Peek(12) == 0x5b;
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
      assert s11.Peek(4) == 0x4c3;
      assert s11.Peek(6) == 0x3a4;
      assert s11.Peek(10) == 0x1c3;
      assert s11.Peek(14) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x2d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x455243313936373a206e657720696d706c656d656e746174696f6e206973206e);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x4c3;
      assert s21.Peek(6) == 0x3a4;
      assert s21.Peek(10) == 0x1c3;
      assert s21.Peek(14) == 0x5b;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 13, 0x1bdd08184818dbdb9d1c9858dd);
      var s24 := Push1(s23, 0x9a);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x4c3;
      assert s31.Peek(4) == 0x3a4;
      assert s31.Peek(8) == 0x1c3;
      assert s31.Peek(12) == 0x5b;
      var s32 := Push2(s31, 0x0331);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s33, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x4c3

    requires s0.stack[4] == 0x3a4

    requires s0.stack[8] == 0x1c3

    requires s0.stack[12] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4c3;
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(8) == 0x1c3;
      assert s1.Peek(12) == 0x5b;
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

  /** Node 141
    * Segment Id for this node is: 98
    * Starting at 0x68e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x4c3

    requires s0.stack[3] == 0x3a4

    requires s0.stack[7] == 0x1c3

    requires s0.stack[11] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c3;
      assert s1.Peek(3) == 0x3a4;
      assert s1.Peek(7) == 0x1c3;
      assert s1.Peek(11) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x0582);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s5, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 88
    * Starting at 0x582
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x582 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x4c3

    requires s0.stack[5] == 0x3a4

    requires s0.stack[9] == 0x1c3

    requires s0.stack[13] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4c3;
      assert s1.Peek(5) == 0x3a4;
      assert s1.Peek(9) == 0x1c3;
      assert s1.Peek(13) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(5) == 0x4c3;
      assert s11.Peek(7) == 0x3a4;
      assert s11.Peek(11) == 0x1c3;
      assert s11.Peek(15) == 0x5b;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Swap3(s15);
      var s17 := Swap1(s16);
      var s18 := Swap3(s17);
      var s19 := And(s18);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x4c3;
      assert s21.Peek(6) == 0x3a4;
      assert s21.Peek(10) == 0x1c3;
      assert s21.Peek(14) == 0x5b;
      var s22 := Swap2(s21);
      var s23 := Or(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s143(s27, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 84
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x3a4

    requires s0.stack[5] == 0x1c3

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a4;
      assert s1.Peek(5) == 0x1c3;
      assert s1.Peek(9) == 0x5b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x3a4;
      assert s11.Peek(7) == 0x1c3;
      assert s11.Peek(11) == 0x5b;
      var s12 := Push32(s11, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s13 := Swap1(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := Log2(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s144(s18, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 69
    * Starting at 0x3a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1c3

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c3;
      assert s1.Peek(7) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x03b1);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s8, gas - 1)
      else
        ExecuteFromCFGNode_s145(s8, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 70
    * Starting at 0x3af
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x1c3;
      assert s1.Peek(7) == 0x5b;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s146(s2, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 71
    * Starting at 0x3b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x01c3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s186(s4, gas - 1)
      else
        ExecuteFromCFGNode_s147(s4, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 72
    * Starting at 0x3b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1c3

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03c0);
      assert s1.Peek(0) == 0x3c0;
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0260);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s5, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 55
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x3c0

    requires s0.stack[6] == 0x1c3

    requires s0.stack[10] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c0;
      assert s1.Peek(6) == 0x1c3;
      assert s1.Peek(10) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0285);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x285;
      assert s11.Peek(9) == 0x3c0;
      assert s11.Peek(13) == 0x1c3;
      assert s11.Peek(17) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x27);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0815);
      var s20 := Push1(s19, 0x27);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x285;
      assert s21.Peek(10) == 0x3c0;
      assert s21.Peek(14) == 0x1c3;
      assert s21.Peek(18) == 0x5b;
      var s22 := CodeCopy(s21);
      var s23 := Push2(s22, 0x041a);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s149(s24, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 76
    * Starting at 0x41a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x285

    requires s0.stack[7] == 0x3c0

    requires s0.stack[11] == 0x1c3

    requires s0.stack[15] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x285;
      assert s1.Peek(7) == 0x3c0;
      assert s1.Peek(11) == 0x1c3;
      assert s1.Peek(15) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup1(s3);
      var s5 := Dup6(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x285;
      assert s11.Peek(11) == 0x3c0;
      assert s11.Peek(15) == 0x1c3;
      assert s11.Peek(19) == 0x5b;
      var s12 := Dup6(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0437);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x07c5);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s150(s19, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 125
    * Starting at 0x7c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[2] == 0x437

    requires s0.stack[10] == 0x285

    requires s0.stack[14] == 0x3c0

    requires s0.stack[18] == 0x1c3

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x437;
      assert s1.Peek(10) == 0x285;
      assert s1.Peek(14) == 0x3c0;
      assert s1.Peek(18) == 0x1c3;
      assert s1.Peek(22) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x07d7);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0799);
      assert s11.Peek(0) == 0x799;
      assert s11.Peek(4) == 0x7d7;
      assert s11.Peek(9) == 0x437;
      assert s11.Peek(17) == 0x285;
      assert s11.Peek(21) == 0x3c0;
      assert s11.Peek(25) == 0x1c3;
      assert s11.Peek(29) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s151(s12, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 120
    * Starting at 0x799
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[3] == 0x7d7

    requires s0.stack[8] == 0x437

    requires s0.stack[16] == 0x285

    requires s0.stack[20] == 0x3c0

    requires s0.stack[24] == 0x1c3

    requires s0.stack[28] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7d7;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x1c3;
      assert s1.Peek(28) == 0x5b;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s152(s2, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 121
    * Starting at 0x79c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x1c3

    requires s0.stack[29] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(17) == 0x285;
      assert s1.Peek(21) == 0x3c0;
      assert s1.Peek(25) == 0x1c3;
      assert s1.Peek(29) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x07b4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s154(s7, gas - 1)
      else
        ExecuteFromCFGNode_s153(s7, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 122
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x1c3

    requires s0.stack[29] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x7d7;
      assert s1.Peek(10) == 0x437;
      assert s1.Peek(18) == 0x285;
      assert s1.Peek(22) == 0x3c0;
      assert s1.Peek(26) == 0x1c3;
      assert s1.Peek(30) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x079c);
      assert s11.Peek(0) == 0x79c;
      assert s11.Peek(5) == 0x7d7;
      assert s11.Peek(10) == 0x437;
      assert s11.Peek(18) == 0x285;
      assert s11.Peek(22) == 0x3c0;
      assert s11.Peek(26) == 0x1c3;
      assert s11.Peek(30) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s12, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 123
    * Starting at 0x7b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x1c3

    requires s0.stack[29] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(17) == 0x285;
      assert s1.Peek(21) == 0x3c0;
      assert s1.Peek(25) == 0x1c3;
      assert s1.Peek(29) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x03c0);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s185(s7, gas - 1)
      else
        ExecuteFromCFGNode_s155(s7, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 124
    * Starting at 0x7bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x1c3

    requires s0.stack[29] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x7d7;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x1c3;
      assert s1.Peek(28) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s7, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 126
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[4] == 0x437

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x437;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x1c3;
      assert s1.Peek(24) == 0x5b;
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
      ExecuteFromCFGNode_s157(s10, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 77
    * Starting at 0x437
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x437 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[8] == 0x285

    requires s0.stack[12] == 0x3c0

    requires s0.stack[16] == 0x1c3

    requires s0.stack[20] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x285;
      assert s1.Peek(12) == 0x3c0;
      assert s1.Peek(16) == 0x1c3;
      assert s1.Peek(20) == 0x5b;
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
      assert s11.Peek(9) == 0x285;
      assert s11.Peek(13) == 0x3c0;
      assert s11.Peek(17) == 0x1c3;
      assert s11.Peek(21) == 0x5b;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x0472);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s184(s21, gas - 1)
      else
        ExecuteFromCFGNode_s158(s21, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 78
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x285

    requires s0.stack[13] == 0x3c0

    requires s0.stack[17] == 0x1c3

    requires s0.stack[21] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x285;
      assert s1.Peek(14) == 0x3c0;
      assert s1.Peek(18) == 0x1c3;
      assert s1.Peek(22) == 0x5b;
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
      assert s11.Peek(11) == 0x285;
      assert s11.Peek(15) == 0x3c0;
      assert s11.Peek(19) == 0x1c3;
      assert s11.Peek(23) == 0x5b;
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
      assert s21.Peek(13) == 0x285;
      assert s21.Peek(17) == 0x3c0;
      assert s21.Peek(21) == 0x1c3;
      assert s21.Peek(25) == 0x5b;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0477);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s159(s25, gas - 1)
  }

  /** Node 159
    * Segment Id for this node is: 80
    * Starting at 0x477
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x477 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x285

    requires s0.stack[13] == 0x3c0

    requires s0.stack[17] == 0x1c3

    requires s0.stack[21] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x285;
      assert s1.Peek(13) == 0x3c0;
      assert s1.Peek(17) == 0x1c3;
      assert s1.Peek(21) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0488);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x488;
      assert s11.Peek(11) == 0x285;
      assert s11.Peek(15) == 0x3c0;
      assert s11.Peek(19) == 0x1c3;
      assert s11.Peek(23) == 0x5b;
      var s12 := Push2(s11, 0x05a3);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s160(s13, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 89
    * Starting at 0x5a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[4] == 0x488

    requires s0.stack[11] == 0x285

    requires s0.stack[15] == 0x3c0

    requires s0.stack[19] == 0x1c3

    requires s0.stack[23] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x488;
      assert s1.Peek(11) == 0x285;
      assert s1.Peek(15) == 0x3c0;
      assert s1.Peek(19) == 0x1c3;
      assert s1.Peek(23) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x060f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s171(s6, gas - 1)
      else
        ExecuteFromCFGNode_s161(s6, gas - 1)
  }

  /** Node 161
    * Segment Id for this node is: 90
    * Starting at 0x5ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x1c3;
      assert s1.Peek(25) == 0x5b;
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x0608);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s4, gas - 1)
      else
        ExecuteFromCFGNode_s162(s4, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 91
    * Starting at 0x5b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x1c3;
      assert s1.Peek(25) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup6(s5);
      var s7 := And(s6);
      var s8 := ExtCodeSize(s7);
      var s9 := Push2(s8, 0x0608);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s10, gas - 1)
      else
        ExecuteFromCFGNode_s163(s10, gas - 1)
  }

  /** Node 163
    * Segment Id for this node is: 92
    * Starting at 0x5c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x1c3;
      assert s1.Peek(25) == 0x5b;
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
      assert s11.Peek(8) == 0x488;
      assert s11.Peek(15) == 0x285;
      assert s11.Peek(19) == 0x3c0;
      assert s11.Peek(23) == 0x1c3;
      assert s11.Peek(27) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(8) == 0x488;
      assert s21.Peek(15) == 0x285;
      assert s21.Peek(19) == 0x3c0;
      assert s21.Peek(23) == 0x1c3;
      assert s21.Peek(27) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0331);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s164(s26, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[6] == 0x488

    requires s0.stack[13] == 0x285

    requires s0.stack[17] == 0x3c0

    requires s0.stack[21] == 0x1c3

    requires s0.stack[25] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x1c3;
      assert s1.Peek(25) == 0x5b;
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

  /** Node 165
    * Segment Id for this node is: 93
    * Starting at 0x608
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x608 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x488;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x1c3;
      assert s1.Peek(24) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0619);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s166(s5, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 95
    * Starting at 0x619
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x619 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x488;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x1c3;
      assert s1.Peek(24) == 0x5b;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s8, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 81
    * Starting at 0x488
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x488 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x285

    requires s0.stack[11] == 0x3c0

    requires s0.stack[15] == 0x1c3

    requires s0.stack[19] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x285;
      assert s1.Peek(11) == 0x3c0;
      assert s1.Peek(15) == 0x1c3;
      assert s1.Peek(19) == 0x5b;
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
      ExecuteFromCFGNode_s168(s10, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 56
    * Starting at 0x285
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x285 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x3c0

    requires s0.stack[8] == 0x1c3

    requires s0.stack[12] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3c0;
      assert s1.Peek(8) == 0x1c3;
      assert s1.Peek(12) == 0x5b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s7, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 73
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s6, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 41
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s5, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 94
    * Starting at 0x60f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x1c3

    requires s0.stack[24] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x488;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x1c3;
      assert s1.Peek(24) == 0x5b;
      var s2 := Push2(s1, 0x0619);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x06b5);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s172(s6, gas - 1)
  }

  /** Node 172
    * Segment Id for this node is: 99
    * Starting at 0x6b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x619

    requires s0.stack[8] == 0x488

    requires s0.stack[15] == 0x285

    requires s0.stack[19] == 0x3c0

    requires s0.stack[23] == 0x1c3

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x619;
      assert s1.Peek(8) == 0x488;
      assert s1.Peek(15) == 0x285;
      assert s1.Peek(19) == 0x3c0;
      assert s1.Peek(23) == 0x1c3;
      assert s1.Peek(27) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x06c5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s6, gas - 1)
      else
        ExecuteFromCFGNode_s173(s6, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 100
    * Starting at 0x6bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x619

    requires s0.stack[8] == 0x488

    requires s0.stack[15] == 0x285

    requires s0.stack[19] == 0x3c0

    requires s0.stack[23] == 0x1c3

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x619;
      assert s1.Peek(9) == 0x488;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x1c3;
      assert s1.Peek(28) == 0x5b;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 174
    * Segment Id for this node is: 101
    * Starting at 0x6c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x619

    requires s0.stack[8] == 0x488

    requires s0.stack[15] == 0x285

    requires s0.stack[19] == 0x3c0

    requires s0.stack[23] == 0x1c3

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x619;
      assert s1.Peek(8) == 0x488;
      assert s1.Peek(15) == 0x285;
      assert s1.Peek(19) == 0x3c0;
      assert s1.Peek(23) == 0x1c3;
      assert s1.Peek(27) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push3(s4, 0x461bcd);
      var s6 := Push1(s5, 0xe5);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x619;
      assert s11.Peek(10) == 0x488;
      assert s11.Peek(17) == 0x285;
      assert s11.Peek(21) == 0x3c0;
      assert s11.Peek(25) == 0x1c3;
      assert s11.Peek(29) == 0x5b;
      var s12 := Push2(s11, 0x0331);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x07e1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s175(s16, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 127
    * Starting at 0x7e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[2] == 0x331

    requires s0.stack[5] == 0x619

    requires s0.stack[11] == 0x488

    requires s0.stack[18] == 0x285

    requires s0.stack[22] == 0x3c0

    requires s0.stack[26] == 0x1c3

    requires s0.stack[30] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x331;
      assert s1.Peek(5) == 0x619;
      assert s1.Peek(11) == 0x488;
      assert s1.Peek(18) == 0x285;
      assert s1.Peek(22) == 0x3c0;
      assert s1.Peek(26) == 0x1c3;
      assert s1.Peek(30) == 0x5b;
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
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(9) == 0x619;
      assert s11.Peek(15) == 0x488;
      assert s11.Peek(22) == 0x285;
      assert s11.Peek(26) == 0x3c0;
      assert s11.Peek(30) == 0x1c3;
      assert s11.Peek(34) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0800);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0799);
      assert s21.Peek(0) == 0x799;
      assert s21.Peek(4) == 0x800;
      assert s21.Peek(9) == 0x331;
      assert s21.Peek(12) == 0x619;
      assert s21.Peek(18) == 0x488;
      assert s21.Peek(25) == 0x285;
      assert s21.Peek(29) == 0x3c0;
      assert s21.Peek(33) == 0x1c3;
      assert s21.Peek(37) == 0x5b;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s176(s22, gas - 1)
  }

  /** Node 176
    * Segment Id for this node is: 120
    * Starting at 0x799
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 38

    requires s0.stack[3] == 0x800

    requires s0.stack[8] == 0x331

    requires s0.stack[11] == 0x619

    requires s0.stack[17] == 0x488

    requires s0.stack[24] == 0x285

    requires s0.stack[28] == 0x3c0

    requires s0.stack[32] == 0x1c3

    requires s0.stack[36] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x800;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(11) == 0x619;
      assert s1.Peek(17) == 0x488;
      assert s1.Peek(24) == 0x285;
      assert s1.Peek(28) == 0x3c0;
      assert s1.Peek(32) == 0x1c3;
      assert s1.Peek(36) == 0x5b;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s177(s2, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 121
    * Starting at 0x79c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x1c3

    requires s0.stack[37] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x800;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(12) == 0x619;
      assert s1.Peek(18) == 0x488;
      assert s1.Peek(25) == 0x285;
      assert s1.Peek(29) == 0x3c0;
      assert s1.Peek(33) == 0x1c3;
      assert s1.Peek(37) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x07b4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s179(s7, gas - 1)
      else
        ExecuteFromCFGNode_s178(s7, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 122
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x1c3

    requires s0.stack[37] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x800;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(13) == 0x619;
      assert s1.Peek(19) == 0x488;
      assert s1.Peek(26) == 0x285;
      assert s1.Peek(30) == 0x3c0;
      assert s1.Peek(34) == 0x1c3;
      assert s1.Peek(38) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x079c);
      assert s11.Peek(0) == 0x79c;
      assert s11.Peek(5) == 0x800;
      assert s11.Peek(10) == 0x331;
      assert s11.Peek(13) == 0x619;
      assert s11.Peek(19) == 0x488;
      assert s11.Peek(26) == 0x285;
      assert s11.Peek(30) == 0x3c0;
      assert s11.Peek(34) == 0x1c3;
      assert s11.Peek(38) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s12, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 123
    * Starting at 0x7b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x1c3

    requires s0.stack[37] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x800;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(12) == 0x619;
      assert s1.Peek(18) == 0x488;
      assert s1.Peek(25) == 0x285;
      assert s1.Peek(29) == 0x3c0;
      assert s1.Peek(33) == 0x1c3;
      assert s1.Peek(37) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x03c0);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s183(s7, gas - 1)
      else
        ExecuteFromCFGNode_s180(s7, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 124
    * Starting at 0x7bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x1c3

    requires s0.stack[37] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x800;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(11) == 0x619;
      assert s1.Peek(17) == 0x488;
      assert s1.Peek(24) == 0x285;
      assert s1.Peek(28) == 0x3c0;
      assert s1.Peek(32) == 0x1c3;
      assert s1.Peek(36) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s7, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 128
    * Starting at 0x800
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x800 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 34

    requires s0.stack[4] == 0x331

    requires s0.stack[7] == 0x619

    requires s0.stack[13] == 0x488

    requires s0.stack[20] == 0x285

    requires s0.stack[24] == 0x3c0

    requires s0.stack[28] == 0x1c3

    requires s0.stack[32] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(7) == 0x619;
      assert s1.Peek(13) == 0x488;
      assert s1.Peek(20) == 0x285;
      assert s1.Peek(24) == 0x3c0;
      assert s1.Peek(28) == 0x1c3;
      assert s1.Peek(32) == 0x5b;
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
      assert s11.Peek(4) == 0x331;
      assert s11.Peek(7) == 0x619;
      assert s11.Peek(13) == 0x488;
      assert s11.Peek(20) == 0x285;
      assert s11.Peek(24) == 0x3c0;
      assert s11.Peek(28) == 0x1c3;
      assert s11.Peek(32) == 0x5b;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s182(s17, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[3] == 0x619

    requires s0.stack[9] == 0x488

    requires s0.stack[16] == 0x285

    requires s0.stack[20] == 0x3c0

    requires s0.stack[24] == 0x1c3

    requires s0.stack[28] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x619;
      assert s1.Peek(9) == 0x488;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x1c3;
      assert s1.Peek(28) == 0x5b;
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

  /** Node 183
    * Segment Id for this node is: 73
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 39

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x1c3

    requires s0.stack[37] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x800;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(12) == 0x619;
      assert s1.Peek(18) == 0x488;
      assert s1.Peek(25) == 0x285;
      assert s1.Peek(29) == 0x3c0;
      assert s1.Peek(33) == 0x1c3;
      assert s1.Peek(37) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s181(s6, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 79
    * Starting at 0x472
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x472 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x285

    requires s0.stack[13] == 0x3c0

    requires s0.stack[17] == 0x1c3

    requires s0.stack[21] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x285;
      assert s1.Peek(13) == 0x3c0;
      assert s1.Peek(17) == 0x1c3;
      assert s1.Peek(21) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s159(s4, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 73
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 31

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x1c3

    requires s0.stack[29] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(17) == 0x285;
      assert s1.Peek(21) == 0x3c0;
      assert s1.Peek(25) == 0x1c3;
      assert s1.Peek(29) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s6, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 41
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1c3

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c3;
      assert s1.Peek(7) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s170(s5, gas - 1)
  }

  /** Node 187
    * Segment Id for this node is: 42
    * Starting at 0x1c8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b;
      var s2 := Push2(s1, 0x01c3);
      var s3 := Push2(s2, 0x00fe);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s188(s4, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 28
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x1c3

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1c3;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push2(s1, 0x0106);
      var s3 := Push2(s2, 0x029b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s189(s4, gas - 1)
  }

  /** Node 189
    * Segment Id for this node is: 58
    * Starting at 0x29b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x1c3

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x1c3;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push2(s1, 0x02a3);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s190(s4, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x2a3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x1c3

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s191(s3, gas - 1)
  }

  /** Node 191
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x2a3

    requires s0.stack[3] == 0x106

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a3;
      assert s1.Peek(3) == 0x106;
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x2a3;
      assert s11.Peek(2) == 0x106;
      assert s11.Peek(3) == 0x1c3;
      assert s11.Peek(7) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s12, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 59
    * Starting at 0x2a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x1c3

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x106;
      assert s11.Peek(6) == 0x1c3;
      assert s11.Peek(10) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0116);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s195(s18, gas - 1)
      else
        ExecuteFromCFGNode_s193(s18, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 60
    * Starting at 0x2bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x1c3

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
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
      assert s11.Peek(3) == 0x106;
      assert s11.Peek(4) == 0x1c3;
      assert s11.Peek(8) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x42);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x106;
      assert s21.Peek(4) == 0x1c3;
      assert s21.Peek(8) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push2(s27, 0x195d);
      var s29 := Push1(s28, 0xf2);
      var s30 := Shl(s29);
      var s31 := Push1(s30, 0x84);
      assert s31.Peek(3) == 0x106;
      assert s31.Peek(4) == 0x1c3;
      assert s31.Peek(8) == 0x5b;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0xa4);
      var s36 := Add(s35);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s194(s36, gas - 1)
  }

  /** Node 194
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x1c3

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
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

  /** Node 195
    * Segment Id for this node is: 31
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x1c3

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x1c3;
      assert s1.Peek(5) == 0x5b;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s196(s2, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 29
    * Starting at 0x106
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[0] == 0x1c3

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1c3;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push2(s1, 0x0116);
      var s3 := Push2(s2, 0x0111);
      var s4 := Push2(s3, 0x033a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s197(s5, gas - 1)
  }

  /** Node 197
    * Segment Id for this node is: 62
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[0] == 0x111

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x1c3

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x111;
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01fb);
      var s4 := Push2(s3, 0x0492);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s198(s5, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 82
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x038c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s5, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x1c3

    requires s0.stack[10] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0x111;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x1c3;
      assert s1.Peek(10) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0x111;
      assert s11.Peek(4) == 0x116;
      assert s11.Peek(5) == 0x1c3;
      assert s11.Peek(9) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s12, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s201(s5, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 30
    * Starting at 0x111
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x1c3

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
      var s2 := Push2(s1, 0x0344);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s202(s3, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 63
    * Starting at 0x344
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x1c3

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x1c3;
      assert s1.Peek(6) == 0x5b;
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
      assert s11.Peek(7) == 0x116;
      assert s11.Peek(8) == 0x1c3;
      assert s11.Peek(12) == 0x5b;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0363);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s204(s21, gas - 1)
      else
        ExecuteFromCFGNode_s203(s21, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 64
    * Starting at 0x35f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x116;
      assert s1.Peek(5) == 0x1c3;
      assert s1.Peek(9) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 204
    * Segment Id for this node is: 65
    * Starting at 0x363
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x363 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x1c3

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x1c3;
      assert s1.Peek(8) == 0x5b;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 205
    * Segment Id for this node is: 11
    * Starting at 0x65
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65 as nat
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
      var s5 := Push2(s4, 0x0071);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s6, gas - 1)
      else
        ExecuteFromCFGNode_s206(s6, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 12
    * Starting at 0x6d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6d as nat
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

  /** Node 207
    * Segment Id for this node is: 13
    * Starting at 0x71
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x71 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x005b);
      var s4 := Push2(s3, 0x0080);
      var s5 := CallDataSize(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Push2(s6, 0x06fb);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s208(s8, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 105
    * Starting at 0x6fb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x80

    requires s0.stack[3] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x80;
      assert s1.Peek(3) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x070d);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s210(s10, gas - 1)
      else
        ExecuteFromCFGNode_s209(s10, gas - 1)
  }

  /** Node 209
    * Segment Id for this node is: 106
    * Starting at 0x709
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x709 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x80

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x80;
      assert s1.Peek(5) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 210
    * Segment Id for this node is: 107
    * Starting at 0x70d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x70d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[3] == 0x80

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x80;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push2(s1, 0x0285);
      var s3 := Dup3(s2);
      var s4 := Push2(s3, 0x06df);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s211(s5, gas - 1)
  }

  /** Node 211
    * Segment Id for this node is: 102
    * Starting at 0x6df
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x285

    requires s0.stack[5] == 0x80

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x285;
      assert s1.Peek(5) == 0x80;
      assert s1.Peek(6) == 0x5b;
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
      assert s11.Peek(4) == 0x285;
      assert s11.Peek(8) == 0x80;
      assert s11.Peek(9) == 0x5b;
      var s12 := Eq(s11);
      var s13 := Push2(s12, 0x06f6);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s213(s14, gas - 1)
      else
        ExecuteFromCFGNode_s212(s14, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 103
    * Starting at 0x6f2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x285

    requires s0.stack[6] == 0x80

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x285;
      assert s1.Peek(7) == 0x80;
      assert s1.Peek(8) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 213
    * Segment Id for this node is: 104
    * Starting at 0x6f6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x285

    requires s0.stack[6] == 0x80

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x285;
      assert s1.Peek(6) == 0x80;
      assert s1.Peek(7) == 0x5b;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s214(s5, gas - 1)
  }

  /** Node 214
    * Segment Id for this node is: 56
    * Starting at 0x285
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x285 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x80

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x80;
      assert s1.Peek(5) == 0x5b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s7, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 14
    * Starting at 0x80
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x80 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x0118);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s216(s3, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 32
    * Starting at 0x118
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x118 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x0120);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s217(s4, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[0] == 0x120

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x120;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s218(s3, gas - 1)
  }

  /** Node 218
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[2] == 0x120

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x120;
      assert s1.Peek(4) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x120;
      assert s11.Peek(3) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s219(s12, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 33
    * Starting at 0x120
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x120 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(6) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0157);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s83(s18, gas - 1)
      else
        ExecuteFromCFGNode_s220(s18, gas - 1)
  }

  /** Node 220
    * Segment Id for this node is: 34
    * Starting at 0x13a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0154);
      assert s1.Peek(0) == 0x154;
      assert s1.Peek(2) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MStore(s8);
      var s10 := Dup1(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x154;
      assert s11.Peek(6) == 0x5b;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Pop(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Push2(s15, 0x039b);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s221(s17, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 68
    * Starting at 0x39b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push2(s1, 0x03a4);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x04ba);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s5, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 83
    * Starting at 0x4ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3a4

    requires s0.stack[5] == 0x154

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a4;
      assert s1.Peek(5) == 0x154;
      assert s1.Peek(7) == 0x5b;
      var s2 := Push2(s1, 0x04c3);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0621);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s223(s5, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 96
    * Starting at 0x621
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x621 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4c3

    requires s0.stack[3] == 0x3a4

    requires s0.stack[7] == 0x154

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c3;
      assert s1.Peek(3) == 0x3a4;
      assert s1.Peek(7) == 0x154;
      assert s1.Peek(9) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := ExtCodeSize(s8);
      var s10 := Push2(s9, 0x068e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s226(s11, gas - 1)
      else
        ExecuteFromCFGNode_s224(s11, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 97
    * Starting at 0x631
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x631 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4c3

    requires s0.stack[3] == 0x3a4

    requires s0.stack[7] == 0x154

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(2) == 0x4c3;
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(8) == 0x154;
      assert s1.Peek(10) == 0x5b;
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
      assert s11.Peek(4) == 0x4c3;
      assert s11.Peek(6) == 0x3a4;
      assert s11.Peek(10) == 0x154;
      assert s11.Peek(12) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x2d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x455243313936373a206e657720696d706c656d656e746174696f6e206973206e);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(4) == 0x4c3;
      assert s21.Peek(6) == 0x3a4;
      assert s21.Peek(10) == 0x154;
      assert s21.Peek(12) == 0x5b;
      var s22 := MStore(s21);
      var s23 := PushN(s22, 13, 0x1bdd08184818dbdb9d1c9858dd);
      var s24 := Push1(s23, 0x9a);
      var s25 := Shl(s24);
      var s26 := Push1(s25, 0x64);
      var s27 := Dup3(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x84);
      var s31 := Add(s30);
      assert s31.Peek(2) == 0x4c3;
      assert s31.Peek(4) == 0x3a4;
      assert s31.Peek(8) == 0x154;
      assert s31.Peek(10) == 0x5b;
      var s32 := Push2(s31, 0x0331);
      var s33 := Jump(s32);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s225(s33, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x4c3

    requires s0.stack[4] == 0x3a4

    requires s0.stack[8] == 0x154

    requires s0.stack[10] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x4c3;
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(8) == 0x154;
      assert s1.Peek(10) == 0x5b;
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

  /** Node 226
    * Segment Id for this node is: 98
    * Starting at 0x68e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4c3

    requires s0.stack[3] == 0x3a4

    requires s0.stack[7] == 0x154

    requires s0.stack[9] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4c3;
      assert s1.Peek(3) == 0x3a4;
      assert s1.Peek(7) == 0x154;
      assert s1.Peek(9) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x0582);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s227(s5, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 88
    * Starting at 0x582
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x582 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x4c3

    requires s0.stack[5] == 0x3a4

    requires s0.stack[9] == 0x154

    requires s0.stack[11] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x4c3;
      assert s1.Peek(5) == 0x3a4;
      assert s1.Peek(9) == 0x154;
      assert s1.Peek(11) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Not(s8);
      var s10 := And(s9);
      var s11 := Push1(s10, 0x01);
      assert s11.Peek(5) == 0x4c3;
      assert s11.Peek(7) == 0x3a4;
      assert s11.Peek(11) == 0x154;
      assert s11.Peek(13) == 0x5b;
      var s12 := Push1(s11, 0x01);
      var s13 := Push1(s12, 0xa0);
      var s14 := Shl(s13);
      var s15 := Sub(s14);
      var s16 := Swap3(s15);
      var s17 := Swap1(s16);
      var s18 := Swap3(s17);
      var s19 := And(s18);
      var s20 := Swap2(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(4) == 0x4c3;
      assert s21.Peek(6) == 0x3a4;
      assert s21.Peek(10) == 0x154;
      assert s21.Peek(12) == 0x5b;
      var s22 := Swap2(s21);
      var s23 := Or(s22);
      var s24 := Swap1(s23);
      var s25 := SStore(s24);
      var s26 := Pop(s25);
      var s27 := Jump(s26);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s228(s27, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 84
    * Starting at 0x4c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3a4

    requires s0.stack[5] == 0x154

    requires s0.stack[7] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a4;
      assert s1.Peek(5) == 0x154;
      assert s1.Peek(7) == 0x5b;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup3(s8);
      var s10 := And(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(3) == 0x3a4;
      assert s11.Peek(7) == 0x154;
      assert s11.Peek(9) == 0x5b;
      var s12 := Push32(s11, 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b);
      var s13 := Swap1(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Swap1(s14);
      var s16 := Log2(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s229(s18, gas - 1)
  }

  /** Node 229
    * Segment Id for this node is: 69
    * Starting at 0x3a4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Gt(s4);
      var s6 := Dup1(s5);
      var s7 := Push2(s6, 0x03b1);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s8, gas - 1)
      else
        ExecuteFromCFGNode_s230(s8, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 70
    * Starting at 0x3af
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3af as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Dup1(s1);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s231(s2, gas - 1)
  }

  /** Node 231
    * Segment Id for this node is: 71
    * Starting at 0x3b1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x01c3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s270(s4, gas - 1)
      else
        ExecuteFromCFGNode_s232(s4, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 72
    * Starting at 0x3b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03c0);
      assert s1.Peek(0) == 0x3c0;
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup4(s2);
      var s4 := Push2(s3, 0x0260);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s233(s5, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 55
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[2] == 0x3c0

    requires s0.stack[6] == 0x154

    requires s0.stack[8] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3c0;
      assert s1.Peek(6) == 0x154;
      assert s1.Peek(8) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Push2(s2, 0x0285);
      var s4 := Dup4(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Dup1(s7);
      var s9 := Push1(s8, 0x60);
      var s10 := Add(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(5) == 0x285;
      assert s11.Peek(9) == 0x3c0;
      assert s11.Peek(13) == 0x154;
      assert s11.Peek(15) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Dup1(s12);
      var s14 := Push1(s13, 0x27);
      var s15 := Dup2(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x20);
      var s18 := Add(s17);
      var s19 := Push2(s18, 0x0815);
      var s20 := Push1(s19, 0x27);
      var s21 := Swap2(s20);
      assert s21.Peek(6) == 0x285;
      assert s21.Peek(10) == 0x3c0;
      assert s21.Peek(14) == 0x154;
      assert s21.Peek(16) == 0x5b;
      var s22 := CodeCopy(s21);
      var s23 := Push2(s22, 0x041a);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s234(s24, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 76
    * Starting at 0x41a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x285

    requires s0.stack[7] == 0x3c0

    requires s0.stack[11] == 0x154

    requires s0.stack[13] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x285;
      assert s1.Peek(7) == 0x3c0;
      assert s1.Peek(11) == 0x154;
      assert s1.Peek(13) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Push1(s2, 0x00);
      var s4 := Dup1(s3);
      var s5 := Dup6(s4);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0xa0);
      var s9 := Shl(s8);
      var s10 := Sub(s9);
      var s11 := And(s10);
      assert s11.Peek(7) == 0x285;
      assert s11.Peek(11) == 0x3c0;
      assert s11.Peek(15) == 0x154;
      assert s11.Peek(17) == 0x5b;
      var s12 := Dup6(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push2(s14, 0x0437);
      var s16 := Swap2(s15);
      var s17 := Swap1(s16);
      var s18 := Push2(s17, 0x07c5);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s235(s19, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 125
    * Starting at 0x7c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x437

    requires s0.stack[10] == 0x285

    requires s0.stack[14] == 0x3c0

    requires s0.stack[18] == 0x154

    requires s0.stack[20] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x437;
      assert s1.Peek(10) == 0x285;
      assert s1.Peek(14) == 0x3c0;
      assert s1.Peek(18) == 0x154;
      assert s1.Peek(20) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := MLoad(s3);
      var s5 := Push2(s4, 0x07d7);
      var s6 := Dup2(s5);
      var s7 := Dup5(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup8(s8);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x0799);
      assert s11.Peek(0) == 0x799;
      assert s11.Peek(4) == 0x7d7;
      assert s11.Peek(9) == 0x437;
      assert s11.Peek(17) == 0x285;
      assert s11.Peek(21) == 0x3c0;
      assert s11.Peek(25) == 0x154;
      assert s11.Peek(27) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s236(s12, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 120
    * Starting at 0x799
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x7d7

    requires s0.stack[8] == 0x437

    requires s0.stack[16] == 0x285

    requires s0.stack[20] == 0x3c0

    requires s0.stack[24] == 0x154

    requires s0.stack[26] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7d7;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x154;
      assert s1.Peek(26) == 0x5b;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s237(s2, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 121
    * Starting at 0x79c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x154

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(17) == 0x285;
      assert s1.Peek(21) == 0x3c0;
      assert s1.Peek(25) == 0x154;
      assert s1.Peek(27) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x07b4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s7, gas - 1)
      else
        ExecuteFromCFGNode_s238(s7, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 122
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x154

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x7d7;
      assert s1.Peek(10) == 0x437;
      assert s1.Peek(18) == 0x285;
      assert s1.Peek(22) == 0x3c0;
      assert s1.Peek(26) == 0x154;
      assert s1.Peek(28) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x079c);
      assert s11.Peek(0) == 0x79c;
      assert s11.Peek(5) == 0x7d7;
      assert s11.Peek(10) == 0x437;
      assert s11.Peek(18) == 0x285;
      assert s11.Peek(22) == 0x3c0;
      assert s11.Peek(26) == 0x154;
      assert s11.Peek(28) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s237(s12, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 123
    * Starting at 0x7b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x154

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(17) == 0x285;
      assert s1.Peek(21) == 0x3c0;
      assert s1.Peek(25) == 0x154;
      assert s1.Peek(27) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x03c0);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s269(s7, gas - 1)
      else
        ExecuteFromCFGNode_s240(s7, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 124
    * Starting at 0x7bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x154

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x7d7;
      assert s1.Peek(8) == 0x437;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x154;
      assert s1.Peek(26) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s7, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 126
    * Starting at 0x7d7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[4] == 0x437

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x437;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x154;
      assert s1.Peek(22) == 0x5b;
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
      ExecuteFromCFGNode_s242(s10, gas - 1)
  }

  /** Node 242
    * Segment Id for this node is: 77
    * Starting at 0x437
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x437 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[8] == 0x285

    requires s0.stack[12] == 0x3c0

    requires s0.stack[16] == 0x154

    requires s0.stack[18] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x285;
      assert s1.Peek(12) == 0x3c0;
      assert s1.Peek(16) == 0x154;
      assert s1.Peek(18) == 0x5b;
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
      assert s11.Peek(9) == 0x285;
      assert s11.Peek(13) == 0x3c0;
      assert s11.Peek(17) == 0x154;
      assert s11.Peek(19) == 0x5b;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := ReturnDataSize(s14);
      var s16 := Dup1(s15);
      var s17 := Push1(s16, 0x00);
      var s18 := Dup2(s17);
      var s19 := Eq(s18);
      var s20 := Push2(s19, 0x0472);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s268(s21, gas - 1)
      else
        ExecuteFromCFGNode_s243(s21, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 78
    * Starting at 0x451
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x451 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[9] == 0x285

    requires s0.stack[13] == 0x3c0

    requires s0.stack[17] == 0x154

    requires s0.stack[19] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(10) == 0x285;
      assert s1.Peek(14) == 0x3c0;
      assert s1.Peek(18) == 0x154;
      assert s1.Peek(20) == 0x5b;
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
      assert s11.Peek(11) == 0x285;
      assert s11.Peek(15) == 0x3c0;
      assert s11.Peek(19) == 0x154;
      assert s11.Peek(21) == 0x5b;
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
      assert s21.Peek(13) == 0x285;
      assert s21.Peek(17) == 0x3c0;
      assert s21.Peek(21) == 0x154;
      assert s21.Peek(23) == 0x5b;
      var s22 := Add(s21);
      var s23 := ReturnDataCopy(s22);
      var s24 := Push2(s23, 0x0477);
      var s25 := Jump(s24);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s244(s25, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 80
    * Starting at 0x477
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x477 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[9] == 0x285

    requires s0.stack[13] == 0x3c0

    requires s0.stack[17] == 0x154

    requires s0.stack[19] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x285;
      assert s1.Peek(13) == 0x3c0;
      assert s1.Peek(17) == 0x154;
      assert s1.Peek(19) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0488);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Dup4(s9);
      var s11 := Dup8(s10);
      assert s11.Peek(4) == 0x488;
      assert s11.Peek(11) == 0x285;
      assert s11.Peek(15) == 0x3c0;
      assert s11.Peek(19) == 0x154;
      assert s11.Peek(21) == 0x5b;
      var s12 := Push2(s11, 0x05a3);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s245(s13, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 89
    * Starting at 0x5a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[4] == 0x488

    requires s0.stack[11] == 0x285

    requires s0.stack[15] == 0x3c0

    requires s0.stack[19] == 0x154

    requires s0.stack[21] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x488;
      assert s1.Peek(11) == 0x285;
      assert s1.Peek(15) == 0x3c0;
      assert s1.Peek(19) == 0x154;
      assert s1.Peek(21) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup4(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x060f);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s255(s6, gas - 1)
      else
        ExecuteFromCFGNode_s246(s6, gas - 1)
  }

  /** Node 246
    * Segment Id for this node is: 90
    * Starting at 0x5ac
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x154;
      assert s1.Peek(23) == 0x5b;
      var s2 := MLoad(s1);
      var s3 := Push2(s2, 0x0608);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s4, gas - 1)
      else
        ExecuteFromCFGNode_s247(s4, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 91
    * Starting at 0x5b2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x01);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x154;
      assert s1.Peek(23) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0xa0);
      var s4 := Shl(s3);
      var s5 := Sub(s4);
      var s6 := Dup6(s5);
      var s7 := And(s6);
      var s8 := ExtCodeSize(s7);
      var s9 := Push2(s8, 0x0608);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s10, gas - 1)
      else
        ExecuteFromCFGNode_s248(s10, gas - 1)
  }

  /** Node 248
    * Segment Id for this node is: 92
    * Starting at 0x5c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x154;
      assert s1.Peek(23) == 0x5b;
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
      assert s11.Peek(8) == 0x488;
      assert s11.Peek(15) == 0x285;
      assert s11.Peek(19) == 0x3c0;
      assert s11.Peek(23) == 0x154;
      assert s11.Peek(25) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x1d);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x416464726573733a2063616c6c20746f206e6f6e2d636f6e7472616374000000);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(8) == 0x488;
      assert s21.Peek(15) == 0x285;
      assert s21.Peek(19) == 0x3c0;
      assert s21.Peek(23) == 0x154;
      assert s21.Peek(25) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Push1(s22, 0x64);
      var s24 := Add(s23);
      var s25 := Push2(s24, 0x0331);
      var s26 := Jump(s25);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s249(s26, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[6] == 0x488

    requires s0.stack[13] == 0x285

    requires s0.stack[17] == 0x3c0

    requires s0.stack[21] == 0x154

    requires s0.stack[23] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x488;
      assert s1.Peek(13) == 0x285;
      assert s1.Peek(17) == 0x3c0;
      assert s1.Peek(21) == 0x154;
      assert s1.Peek(23) == 0x5b;
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

  /** Node 250
    * Segment Id for this node is: 93
    * Starting at 0x608
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x608 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x488;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x154;
      assert s1.Peek(22) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x0619);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s251(s5, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 95
    * Starting at 0x619
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x619 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x488;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x154;
      assert s1.Peek(22) == 0x5b;
      var s2 := Swap5(s1);
      var s3 := Swap4(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s252(s8, gas - 1)
  }

  /** Node 252
    * Segment Id for this node is: 81
    * Starting at 0x488
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x488 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x285

    requires s0.stack[11] == 0x3c0

    requires s0.stack[15] == 0x154

    requires s0.stack[17] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x285;
      assert s1.Peek(11) == 0x3c0;
      assert s1.Peek(15) == 0x154;
      assert s1.Peek(17) == 0x5b;
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
      ExecuteFromCFGNode_s253(s10, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 56
    * Starting at 0x285
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x285 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0x3c0

    requires s0.stack[8] == 0x154

    requires s0.stack[10] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x3c0;
      assert s1.Peek(8) == 0x154;
      assert s1.Peek(10) == 0x5b;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s7, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 73
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[4] == 0x154

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x154;
      assert s1.Peek(6) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s6, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 94
    * Starting at 0x60f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[5] == 0x488

    requires s0.stack[12] == 0x285

    requires s0.stack[16] == 0x3c0

    requires s0.stack[20] == 0x154

    requires s0.stack[22] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x488;
      assert s1.Peek(12) == 0x285;
      assert s1.Peek(16) == 0x3c0;
      assert s1.Peek(20) == 0x154;
      assert s1.Peek(22) == 0x5b;
      var s2 := Push2(s1, 0x0619);
      var s3 := Dup4(s2);
      var s4 := Dup4(s3);
      var s5 := Push2(s4, 0x06b5);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s6, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 99
    * Starting at 0x6b5
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6b5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x619

    requires s0.stack[8] == 0x488

    requires s0.stack[15] == 0x285

    requires s0.stack[19] == 0x3c0

    requires s0.stack[23] == 0x154

    requires s0.stack[25] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x619;
      assert s1.Peek(8) == 0x488;
      assert s1.Peek(15) == 0x285;
      assert s1.Peek(19) == 0x3c0;
      assert s1.Peek(23) == 0x154;
      assert s1.Peek(25) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := IsZero(s3);
      var s5 := Push2(s4, 0x06c5);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s258(s6, gas - 1)
      else
        ExecuteFromCFGNode_s257(s6, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 100
    * Starting at 0x6bd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x619

    requires s0.stack[8] == 0x488

    requires s0.stack[15] == 0x285

    requires s0.stack[19] == 0x3c0

    requires s0.stack[23] == 0x154

    requires s0.stack[25] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(3) == 0x619;
      assert s1.Peek(9) == 0x488;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x154;
      assert s1.Peek(26) == 0x5b;
      var s2 := MLoad(s1);
      var s3 := Dup1(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 258
    * Segment Id for this node is: 101
    * Starting at 0x6c5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 27

    requires s0.stack[2] == 0x619

    requires s0.stack[8] == 0x488

    requires s0.stack[15] == 0x285

    requires s0.stack[19] == 0x3c0

    requires s0.stack[23] == 0x154

    requires s0.stack[25] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x619;
      assert s1.Peek(8) == 0x488;
      assert s1.Peek(15) == 0x285;
      assert s1.Peek(19) == 0x3c0;
      assert s1.Peek(23) == 0x154;
      assert s1.Peek(25) == 0x5b;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Push3(s4, 0x461bcd);
      var s6 := Push1(s5, 0xe5);
      var s7 := Shl(s6);
      var s8 := Dup2(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x04);
      var s11 := Add(s10);
      assert s11.Peek(4) == 0x619;
      assert s11.Peek(10) == 0x488;
      assert s11.Peek(17) == 0x285;
      assert s11.Peek(21) == 0x3c0;
      assert s11.Peek(25) == 0x154;
      assert s11.Peek(27) == 0x5b;
      var s12 := Push2(s11, 0x0331);
      var s13 := Swap2(s12);
      var s14 := Swap1(s13);
      var s15 := Push2(s14, 0x07e1);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s259(s16, gas - 1)
  }

  /** Node 259
    * Segment Id for this node is: 127
    * Starting at 0x7e1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7e1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[2] == 0x331

    requires s0.stack[5] == 0x619

    requires s0.stack[11] == 0x488

    requires s0.stack[18] == 0x285

    requires s0.stack[22] == 0x3c0

    requires s0.stack[26] == 0x154

    requires s0.stack[28] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x331;
      assert s1.Peek(5) == 0x619;
      assert s1.Peek(11) == 0x488;
      assert s1.Peek(18) == 0x285;
      assert s1.Peek(22) == 0x3c0;
      assert s1.Peek(26) == 0x154;
      assert s1.Peek(28) == 0x5b;
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
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(9) == 0x619;
      assert s11.Peek(15) == 0x488;
      assert s11.Peek(22) == 0x285;
      assert s11.Peek(26) == 0x3c0;
      assert s11.Peek(30) == 0x154;
      assert s11.Peek(32) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push2(s12, 0x0800);
      var s14 := Dup2(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := Dup6(s15);
      var s17 := Add(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Dup8(s18);
      var s20 := Add(s19);
      var s21 := Push2(s20, 0x0799);
      assert s21.Peek(0) == 0x799;
      assert s21.Peek(4) == 0x800;
      assert s21.Peek(9) == 0x331;
      assert s21.Peek(12) == 0x619;
      assert s21.Peek(18) == 0x488;
      assert s21.Peek(25) == 0x285;
      assert s21.Peek(29) == 0x3c0;
      assert s21.Peek(33) == 0x154;
      assert s21.Peek(35) == 0x5b;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s260(s22, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 120
    * Starting at 0x799
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x799 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 36

    requires s0.stack[3] == 0x800

    requires s0.stack[8] == 0x331

    requires s0.stack[11] == 0x619

    requires s0.stack[17] == 0x488

    requires s0.stack[24] == 0x285

    requires s0.stack[28] == 0x3c0

    requires s0.stack[32] == 0x154

    requires s0.stack[34] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x800;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(11) == 0x619;
      assert s1.Peek(17) == 0x488;
      assert s1.Peek(24) == 0x285;
      assert s1.Peek(28) == 0x3c0;
      assert s1.Peek(32) == 0x154;
      assert s1.Peek(34) == 0x5b;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s261(s2, gas - 1)
  }

  /** Node 261
    * Segment Id for this node is: 121
    * Starting at 0x79c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x154

    requires s0.stack[35] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x800;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(12) == 0x619;
      assert s1.Peek(18) == 0x488;
      assert s1.Peek(25) == 0x285;
      assert s1.Peek(29) == 0x3c0;
      assert s1.Peek(33) == 0x154;
      assert s1.Peek(35) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x07b4);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s7, gas - 1)
      else
        ExecuteFromCFGNode_s262(s7, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 122
    * Starting at 0x7a5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x154

    requires s0.stack[35] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(5) == 0x800;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(13) == 0x619;
      assert s1.Peek(19) == 0x488;
      assert s1.Peek(26) == 0x285;
      assert s1.Peek(30) == 0x3c0;
      assert s1.Peek(34) == 0x154;
      assert s1.Peek(36) == 0x5b;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := MLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Push2(s10, 0x079c);
      assert s11.Peek(0) == 0x79c;
      assert s11.Peek(5) == 0x800;
      assert s11.Peek(10) == 0x331;
      assert s11.Peek(13) == 0x619;
      assert s11.Peek(19) == 0x488;
      assert s11.Peek(26) == 0x285;
      assert s11.Peek(30) == 0x3c0;
      assert s11.Peek(34) == 0x154;
      assert s11.Peek(36) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s261(s12, gas - 1)
  }

  /** Node 263
    * Segment Id for this node is: 123
    * Starting at 0x7b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x154

    requires s0.stack[35] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x800;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(12) == 0x619;
      assert s1.Peek(18) == 0x488;
      assert s1.Peek(25) == 0x285;
      assert s1.Peek(29) == 0x3c0;
      assert s1.Peek(33) == 0x154;
      assert s1.Peek(35) == 0x5b;
      var s2 := Dup4(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x03c0);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s267(s7, gas - 1)
      else
        ExecuteFromCFGNode_s264(s7, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 124
    * Starting at 0x7bd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x154

    requires s0.stack[35] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Pop(s0);
      assert s1.Peek(3) == 0x800;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(11) == 0x619;
      assert s1.Peek(17) == 0x488;
      assert s1.Peek(24) == 0x285;
      assert s1.Peek(28) == 0x3c0;
      assert s1.Peek(32) == 0x154;
      assert s1.Peek(34) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Swap2(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s7, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 128
    * Starting at 0x800
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x800 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[4] == 0x331

    requires s0.stack[7] == 0x619

    requires s0.stack[13] == 0x488

    requires s0.stack[20] == 0x285

    requires s0.stack[24] == 0x3c0

    requires s0.stack[28] == 0x154

    requires s0.stack[30] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(7) == 0x619;
      assert s1.Peek(13) == 0x488;
      assert s1.Peek(20) == 0x285;
      assert s1.Peek(24) == 0x3c0;
      assert s1.Peek(28) == 0x154;
      assert s1.Peek(30) == 0x5b;
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
      assert s11.Peek(4) == 0x331;
      assert s11.Peek(7) == 0x619;
      assert s11.Peek(13) == 0x488;
      assert s11.Peek(20) == 0x285;
      assert s11.Peek(24) == 0x3c0;
      assert s11.Peek(28) == 0x154;
      assert s11.Peek(30) == 0x5b;
      var s12 := Add(s11);
      var s13 := Swap3(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s17, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[3] == 0x619

    requires s0.stack[9] == 0x488

    requires s0.stack[16] == 0x285

    requires s0.stack[20] == 0x3c0

    requires s0.stack[24] == 0x154

    requires s0.stack[26] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x619;
      assert s1.Peek(9) == 0x488;
      assert s1.Peek(16) == 0x285;
      assert s1.Peek(20) == 0x3c0;
      assert s1.Peek(24) == 0x154;
      assert s1.Peek(26) == 0x5b;
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
    * Segment Id for this node is: 73
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 37

    requires s0.stack[4] == 0x800

    requires s0.stack[9] == 0x331

    requires s0.stack[12] == 0x619

    requires s0.stack[18] == 0x488

    requires s0.stack[25] == 0x285

    requires s0.stack[29] == 0x3c0

    requires s0.stack[33] == 0x154

    requires s0.stack[35] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x800;
      assert s1.Peek(9) == 0x331;
      assert s1.Peek(12) == 0x619;
      assert s1.Peek(18) == 0x488;
      assert s1.Peek(25) == 0x285;
      assert s1.Peek(29) == 0x3c0;
      assert s1.Peek(33) == 0x154;
      assert s1.Peek(35) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s265(s6, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 79
    * Starting at 0x472
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x472 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[9] == 0x285

    requires s0.stack[13] == 0x3c0

    requires s0.stack[17] == 0x154

    requires s0.stack[19] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x285;
      assert s1.Peek(13) == 0x3c0;
      assert s1.Peek(17) == 0x154;
      assert s1.Peek(19) == 0x5b;
      var s2 := Push1(s1, 0x60);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s244(s4, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 73
    * Starting at 0x3c0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[4] == 0x7d7

    requires s0.stack[9] == 0x437

    requires s0.stack[17] == 0x285

    requires s0.stack[21] == 0x3c0

    requires s0.stack[25] == 0x154

    requires s0.stack[27] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d7;
      assert s1.Peek(9) == 0x437;
      assert s1.Peek(17) == 0x285;
      assert s1.Peek(21) == 0x3c0;
      assert s1.Peek(25) == 0x154;
      assert s1.Peek(27) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s6, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 41
    * Starting at 0x1c3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x154

    requires s0.stack[5] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x154;
      assert s1.Peek(5) == 0x5b;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s81(s5, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 7
    * Starting at 0x4e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x005d);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s290(s4, gas - 1)
      else
        ExecuteFromCFGNode_s272(s4, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 8
    * Starting at 0x54
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x005b);
      assert s1.Peek(0) == 0x5b;
      var s2 := Push2(s1, 0x00fe);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s3, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 28
    * Starting at 0xfe
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xfe as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5b;
      var s2 := Push2(s1, 0x0106);
      var s3 := Push2(s2, 0x029b);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s274(s4, gas - 1)
  }

  /** Node 274
    * Segment Id for this node is: 58
    * Starting at 0x29b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x5b;
      var s2 := Push2(s1, 0x02a3);
      var s3 := Push2(s2, 0x0368);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s275(s4, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 66
    * Starting at 0x368
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x368 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x2a3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2a3;
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s276(s3, gas - 1)
  }

  /** Node 276
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x2a3

    requires s0.stack[3] == 0x106

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2a3;
      assert s1.Peek(3) == 0x106;
      assert s1.Peek(4) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x2a3;
      assert s11.Peek(2) == 0x106;
      assert s11.Peek(3) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s277(s12, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 59
    * Starting at 0x2a3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := And(s6);
      var s8 := Caller(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Push1(s9, 0x01);
      var s11 := Push1(s10, 0xa0);
      assert s11.Peek(5) == 0x106;
      assert s11.Peek(6) == 0x5b;
      var s12 := Shl(s11);
      var s13 := Sub(s12);
      var s14 := And(s13);
      var s15 := Eq(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x0116);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s280(s18, gas - 1)
      else
        ExecuteFromCFGNode_s278(s18, gas - 1)
  }

  /** Node 278
    * Segment Id for this node is: 60
    * Starting at 0x2bd
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2bd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
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
      assert s11.Peek(3) == 0x106;
      assert s11.Peek(4) == 0x5b;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x42);
      var s14 := Push1(s13, 0x24);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Push32(s17, 0x5472616e73706172656e745570677261646561626c6550726f78793a2061646d);
      var s19 := Push1(s18, 0x44);
      var s20 := Dup3(s19);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x106;
      assert s21.Peek(4) == 0x5b;
      var s22 := MStore(s21);
      var s23 := Push32(s22, 0x696e2063616e6e6f742066616c6c6261636b20746f2070726f78792074617267);
      var s24 := Push1(s23, 0x64);
      var s25 := Dup3(s24);
      var s26 := Add(s25);
      var s27 := MStore(s26);
      var s28 := Push2(s27, 0x195d);
      var s29 := Push1(s28, 0xf2);
      var s30 := Shl(s29);
      var s31 := Push1(s30, 0x84);
      assert s31.Peek(3) == 0x106;
      assert s31.Peek(4) == 0x5b;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0xa4);
      var s36 := Add(s35);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s279(s36, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x106

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x106;
      assert s1.Peek(2) == 0x5b;
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

  /** Node 280
    * Segment Id for this node is: 31
    * Starting at 0x116
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x116 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x106

    requires s0.stack[1] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x106;
      assert s1.Peek(1) == 0x5b;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s281(s2, gas - 1)
  }

  /** Node 281
    * Segment Id for this node is: 29
    * Starting at 0x106
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    requires s0.stack[0] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x5b;
      var s2 := Push2(s1, 0x0116);
      var s3 := Push2(s2, 0x0111);
      var s4 := Push2(s3, 0x033a);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s5, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 62
    * Starting at 0x33a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[0] == 0x111

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x111;
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01fb);
      var s4 := Push2(s3, 0x0492);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s283(s5, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 82
    * Starting at 0x492
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x492 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[0] == 0x1fb

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x1fb;
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Push32(s2, 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc);
      var s4 := Push2(s3, 0x038c);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s284(s5, gas - 1)
  }

  /** Node 284
    * Segment Id for this node is: 67
    * Starting at 0x38c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x38c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x1fb

    requires s0.stack[4] == 0x111

    requires s0.stack[5] == 0x116

    requires s0.stack[6] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1fb;
      assert s1.Peek(4) == 0x111;
      assert s1.Peek(5) == 0x116;
      assert s1.Peek(6) == 0x5b;
      var s2 := SLoad(s1);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0xa0);
      var s6 := Shl(s5);
      var s7 := Sub(s6);
      var s8 := And(s7);
      var s9 := Swap2(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(0) == 0x1fb;
      assert s11.Peek(3) == 0x111;
      assert s11.Peek(4) == 0x116;
      assert s11.Peek(5) == 0x5b;
      var s12 := Jump(s11);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s12, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 46
    * Starting at 0x1fb
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x111

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x111;
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x5b;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s286(s5, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 30
    * Starting at 0x111
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x5b;
      var s2 := Push2(s1, 0x0344);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s287(s3, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 63
    * Starting at 0x344
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x116

    requires s0.stack[2] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x116;
      assert s1.Peek(2) == 0x5b;
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
      assert s11.Peek(7) == 0x116;
      assert s11.Peek(8) == 0x5b;
      var s12 := DelegateCall(s11);
      var s13 := ReturnDataSize(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Dup1(s14);
      var s16 := ReturnDataCopy(s15);
      var s17 := Dup1(s16);
      var s18 := Dup1(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0363);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s289(s21, gas - 1)
      else
        ExecuteFromCFGNode_s288(s21, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 64
    * Starting at 0x35f
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x35f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(4) == 0x116;
      assert s1.Peek(5) == 0x5b;
      var s2 := Push1(s1, 0x00);
      var s3 := Return(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 289
    * Segment Id for this node is: 65
    * Starting at 0x363
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x363 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x116

    requires s0.stack[4] == 0x5b

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x116;
      assert s1.Peek(4) == 0x5b;
      var s2 := ReturnDataSize(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 290
    * Segment Id for this node is: 10
    * Starting at 0x5d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x005b);
      var s3 := Push2(s2, 0x00fe);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s273(s4, gas - 1)
  }
}
