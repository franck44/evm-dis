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
      var s6 := Push2(s5, 0x00ea);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s348(s7, gas - 1)
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
      var s6 := Push4(s5, 0x5e9d4044);
      var s7 := Gt(s6);
      var s8 := Push2(s7, 0x008c);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s233(s9, gas - 1)
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
      var s2 := Push4(s1, 0x87b1bb11);
      var s3 := Gt(s2);
      var s4 := Push2(s3, 0x0066);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s134(s5, gas - 1)
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
      var s2 := Push4(s1, 0x87b1bb11);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0422);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s116(s5, gas - 1)
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
      var s2 := Push4(s1, 0xc56710ff);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x042a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s92(s5, gas - 1)
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
      var s2 := Push4(s1, 0xd6cd921e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x04d0);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s5, gas - 1)
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
      var s2 := Push4(s1, 0xf8ccb33c);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x058e);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s5, gas - 1)
      else
        ExecuteFromCFGNode_s9(s5, gas - 1)
  }

  /** Node 9
    * Segment Id for this node is: 9
    * Starting at 0x62
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x00ea);
      assert s1.Peek(0) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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

  /** Node 11
    * Segment Id for this node is: 96
    * Starting at 0x58e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0288);
      var s3 := Push2(s2, 0x0f72);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s4, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 164
    * Starting at 0xf72
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x288;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x1f);
      var s11 := Dup2(s10);
      assert s11.Peek(4) == 0x288;
      var s12 := MStore(s11);
      var s13 := Push32(s12, 0x6e6f64652e766f74696e672e706f7765722e7374616b652e6d6178696d756d00);
      var s14 := Push1(s13, 0x20);
      var s15 := Swap2(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := MStore(s17);
      var s19 := Dup2(s18);
      var s20 := MLoad(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(4) == 0x288;
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Swap3(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x16);
      var s28 := Dup3(s27);
      var s29 := MStore(s28);
      var s30 := Push32(s29, 0x726f636b65744e6574776f726b536e617073686f747300000000000000000000);
      var s31 := Swap1(s30);
      assert s31.Peek(3) == 0x288;
      var s32 := Dup3(s31);
      var s33 := Add(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x00);
      var s36 := Swap1(s35);
      var s37 := Push32(s36, 0x1b6028195e85a43527189139611db98fd210d645ea6839e6c06effd45b5934a9);
      var s38 := Swap1(s37);
      var s39 := Dup3(s38);
      var s40 := Swap1(s39);
      var s41 := Push2(s40, 0x1007);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s13(s41, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 165
    * Starting at 0x1002
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1002 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[0] == 0x1007

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(1) == 0x1007;
      assert s1.Peek(5) == 0x288;
      var s2 := Push2(s1, 0x11c5);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s3, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 185
    * Starting at 0x11c5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x1007

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1007;
      assert s1.Peek(5) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1284);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x1284;
      assert s11.Peek(8) == 0x1007;
      assert s11.Peek(12) == 0x288;
      var s12 := Push32(s11, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x10);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x1284;
      assert s21.Peek(9) == 0x1007;
      assert s21.Peek(13) == 0x288;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup1(s24);
      var s26 := Dup4(s25);
      var s27 := Dup4(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s15(s27, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 186
    * Starting at 0x1207
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x1007

    requires s0.stack[16] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0x1007;
      assert s1.Peek(16) == 0x288;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x1244);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s6, gas - 1)
      else
        ExecuteFromCFGNode_s16(s6, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 187
    * Starting at 0x1210
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x1007

    requires s0.stack[16] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0x1007;
      assert s1.Peek(17) == 0x288;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0x1284;
      assert s11.Peek(13) == 0x1007;
      assert s11.Peek(17) == 0x288;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x1207);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s15(s17, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 188
    * Starting at 0x1244
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x1007

    requires s0.stack[16] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0x1007;
      assert s1.Peek(16) == 0x288;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x1284;
      assert s11.Peek(15) == 0x1007;
      assert s11.Peek(19) == 0x288;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(13) == 0x1284;
      assert s21.Peek(17) == 0x1007;
      assert s21.Peek(21) == 0x288;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x1284;
      assert s31.Peek(7) == 0x1007;
      assert s31.Peek(11) == 0x288;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MLoad(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Dup2(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s18(s41, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 189
    * Starting at 0x1273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1284

    requires s0.stack[7] == 0x1007

    requires s0.stack[11] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0x1007;
      assert s1.Peek(12) == 0x288;
      var s2 := MStore(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MStore(s4);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x1284;
      assert s11.Peek(5) == 0x1007;
      assert s11.Peek(9) == 0x288;
      var s12 := Push2(s11, 0x10ab);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s13, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 174
    * Starting at 0x10ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1284

    requires s0.stack[5] == 0x1007

    requires s0.stack[9] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1284;
      assert s1.Peek(5) == 0x1007;
      assert s1.Peek(9) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x1284;
      assert s11.Peek(7) == 0x1007;
      assert s11.Peek(11) == 0x288;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x21f8a721);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x1284;
      assert s21.Peek(12) == 0x1007;
      assert s21.Peek(16) == 0x288;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x1284;
      assert s31.Peek(13) == 0x1007;
      assert s31.Peek(17) == 0x288;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s20(s41, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 175
    * Starting at 0x110e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x1007

    requires s0.stack[16] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0x1007;
      assert s1.Peek(17) == 0x288;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s11, gas - 1)
      else
        ExecuteFromCFGNode_s21(s11, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 176
    * Starting at 0x111b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0x1007

    requires s0.stack[19] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1284;
      assert s1.Peek(16) == 0x1007;
      assert s1.Peek(20) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0x1007

    requires s0.stack[19] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1284;
      assert s1.Peek(15) == 0x1007;
      assert s1.Peek(19) == 0x288;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s24(s9, gas - 1)
      else
        ExecuteFromCFGNode_s23(s9, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0x1007

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1284;
      assert s1.Peek(11) == 0x1007;
      assert s1.Peek(15) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 24
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0x1007

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1284;
      assert s1.Peek(10) == 0x1007;
      assert s1.Peek(14) == 0x288;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x1284;
      assert s11.Peek(9) == 0x1007;
      assert s11.Peek(13) == 0x288;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s26(s14, gas - 1)
      else
        ExecuteFromCFGNode_s25(s14, gas - 1)
  }

  /** Node 25
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0x1007

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1284;
      assert s1.Peek(9) == 0x1007;
      assert s1.Peek(13) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 26
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0x1007

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0x1007;
      assert s1.Peek(12) == 0x288;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s8, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 190
    * Starting at 0x1284
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1007

    requires s0.stack[8] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1007;
      assert s1.Peek(8) == 0x288;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x065e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s29(s8, gas - 1)
      else
        ExecuteFromCFGNode_s28(s8, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 191
    * Starting at 0x12a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1007

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x1007;
      assert s1.Peek(8) == 0x288;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x1007;
      assert s11.Peek(9) == 0x288;
      var s12 := Push1(s11, 0x12);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(5) == 0x1007;
      assert s21.Peek(9) == 0x288;
      var s22 := Swap1(s21);
      var s23 := MLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := Swap1(s25);
      var s27 := Sub(s26);
      var s28 := Push1(s27, 0x64);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Revert(s30);
      // Segment is terminal (Revert, Stop or Return)
      s31
  }

  /** Node 29
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1007

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1007;
      assert s1.Peek(7) == 0x288;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s6, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 166
    * Starting at 0x1007
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +9
    * Net Capacity Effect: -9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1007 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x288;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push4(s6, 0x6838444b);
      var s8 := Dup4(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MLoad(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(8) == 0x288;
      var s12 := Push4(s11, 0xffffffff);
      var s13 := And(s12);
      var s14 := Push1(s13, 0xe0);
      var s15 := Shl(s14);
      var s16 := Dup2(s15);
      var s17 := MStore(s16);
      var s18 := Push1(s17, 0x04);
      var s19 := Add(s18);
      var s20 := Dup1(s19);
      var s21 := Dup3(s20);
      assert s21.Peek(9) == 0x288;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Push1(s23, 0x20);
      var s25 := Add(s24);
      var s26 := Swap2(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Push1(s28, 0x20);
      var s30 := Push1(s29, 0x40);
      var s31 := MLoad(s30);
      assert s31.Peek(8) == 0x288;
      var s32 := Dup1(s31);
      var s33 := Dup4(s32);
      var s34 := Sub(s33);
      var s35 := Dup2(s34);
      var s36 := Dup7(s35);
      var s37 := Dup1(s36);
      var s38 := ExtCodeSize(s37);
      var s39 := IsZero(s38);
      var s40 := Dup1(s39);
      var s41 := IsZero(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s31(s41, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 167
    * Starting at 0x1052
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1052 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[13] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x105a);
      assert s1.Peek(0) == 0x105a;
      assert s1.Peek(14) == 0x288;
      var s2 := JumpI(s1);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s1.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s2, gas - 1)
      else
        ExecuteFromCFGNode_s32(s2, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 168
    * Starting at 0x1056
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1056 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 169
    * Starting at 0x105a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x105a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x288;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x106e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s9, gas - 1)
      else
        ExecuteFromCFGNode_s34(s9, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 170
    * Starting at 0x1065
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1065 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(8) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 35
    * Segment Id for this node is: 171
    * Starting at 0x106e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x106e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x288;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(6) == 0x288;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1084);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s37(s14, gas - 1)
      else
        ExecuteFromCFGNode_s36(s14, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 172
    * Starting at 0x1080
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1080 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 37
    * Segment Id for this node is: 173
    * Starting at 0x1084
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1084 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x288;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := PushN(s3, 28, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := And(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s11, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 48
    * Starting at 0x288
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x288 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := Swap1(s10);
      var s12 := Sub(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Swap1(s14);
      var s16 := Return(s15);
      // Segment is terminal (Revert, Stop or Return)
      s16
  }

  /** Node 39
    * Segment Id for this node is: 86
    * Starting at 0x4d0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0342);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x04e6);
      assert s11.Peek(0) == 0x4e6;
      assert s11.Peek(4) == 0x342;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s41(s12, gas - 1)
      else
        ExecuteFromCFGNode_s40(s12, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 87
    * Starting at 0x4e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 41
    * Segment Id for this node is: 88
    * Starting at 0x4e6
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 5, 0x0100000000);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x342;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x0501);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s15, gas - 1)
      else
        ExecuteFromCFGNode_s42(s15, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 89
    * Starting at 0x4fd
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4fd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 43
    * Segment Id for this node is: 90
    * Starting at 0x501
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x501 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x0513);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s11, gas - 1)
      else
        ExecuteFromCFGNode_s44(s11, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 91
    * Starting at 0x50f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 45
    * Segment Id for this node is: 92
    * Starting at 0x513
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x513 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0x342;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 5, 0x0100000000);
      var s16 := Dup4(s15);
      var s17 := Gt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0535);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s47(s21, gas - 1)
      else
        ExecuteFromCFGNode_s46(s21, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 93
    * Starting at 0x531
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x531 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 47
    * Segment Id for this node is: 94
    * Starting at 0x535
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x535 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x342;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup1(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Div(s10);
      assert s11.Peek(8) == 0x342;
      var s12 := Mul(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0x342;
      var s22 := Dup1(s21);
      var s23 := Swap4(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x342;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      var s34 := Dup1(s33);
      var s35 := Dup3(s34);
      var s36 := Dup5(s35);
      var s37 := CallDataCopy(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s48(s41, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 95
    * Starting at 0x565
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x565 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(10) == 0x342;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Swap1(s9);
      var s11 := CallDataLoad(s10);
      assert s11.Peek(4) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Push2(s15, 0x0db4);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Jump(s18);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s19, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 153
    * Starting at 0xdb4
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdb4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Push2(s1, 0x0e0d);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0xe0d;
      assert s11.Peek(8) == 0x342;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Dup1(s14);
      var s16 := Push32(s15, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x08);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0xe0d;
      assert s21.Peek(6) == 0x342;
      var s22 := Swap2(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Dup2(s27);
      var s29 := Dup4(s28);
      var s30 := Sub(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0xe0d;
      assert s31.Peek(6) == 0x342;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MStore(s35);
      var s37 := Dup1(s36);
      var s38 := MLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s50(s41, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 154
    * Starting at 0xe08
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe08 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0xe0d

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0x342;
      var s2 := Push2(s1, 0x1151);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s3, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 182
    * Starting at 0x1151
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0xe0d

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe0d;
      assert s1.Peek(4) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0xe0d;
      assert s11.Peek(6) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x7ae1cfca);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0xe0d;
      assert s21.Peek(11) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0xe0d;
      assert s31.Peek(12) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s52(s41, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 183
    * Starting at 0x11b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0xe0d

    requires s0.stack[11] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0xe0d;
      assert s1.Peek(12) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s54(s11, gas - 1)
      else
        ExecuteFromCFGNode_s53(s11, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 184
    * Starting at 0x11c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0xe0d

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0xe0d;
      assert s1.Peek(15) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 54
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0xe0d

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0xe0d;
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s56(s9, gas - 1)
      else
        ExecuteFromCFGNode_s55(s9, gas - 1)
  }

  /** Node 55
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0xe0d

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xe0d;
      assert s1.Peek(10) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 56
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0xe0d

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xe0d;
      assert s1.Peek(9) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0xe0d;
      assert s11.Peek(8) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s14, gas - 1)
      else
        ExecuteFromCFGNode_s57(s14, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0xe0d

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xe0d;
      assert s1.Peek(8) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 58
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0xe0d

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe0d;
      assert s1.Peek(7) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s8, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 155
    * Starting at 0xe0d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0ed3);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s4, gas - 1)
      else
        ExecuteFromCFGNode_s60(s4, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 156
    * Starting at 0xe13
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe13 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0e67);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xe67;
      assert s11.Peek(5) == 0x342;
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
      assert s21.Peek(1) == 0xe67;
      assert s21.Peek(5) == 0x342;
      var s22 := Push2(s21, 0x11c5);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s23, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 185
    * Starting at 0x11c5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xe67

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xe67;
      assert s1.Peek(5) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1284);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x1284;
      assert s11.Peek(8) == 0xe67;
      assert s11.Peek(12) == 0x342;
      var s12 := Push32(s11, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x10);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x1284;
      assert s21.Peek(9) == 0xe67;
      assert s21.Peek(13) == 0x342;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup1(s24);
      var s26 := Dup4(s25);
      var s27 := Dup4(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s62(s27, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 186
    * Starting at 0x1207
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xe67

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0xe67;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x1244);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s64(s6, gas - 1)
      else
        ExecuteFromCFGNode_s63(s6, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 187
    * Starting at 0x1210
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xe67

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0xe67;
      assert s1.Peek(17) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0x1284;
      assert s11.Peek(13) == 0xe67;
      assert s11.Peek(17) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x1207);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s17, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 188
    * Starting at 0x1244
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xe67

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0xe67;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x1284;
      assert s11.Peek(15) == 0xe67;
      assert s11.Peek(19) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(13) == 0x1284;
      assert s21.Peek(17) == 0xe67;
      assert s21.Peek(21) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x1284;
      assert s31.Peek(7) == 0xe67;
      assert s31.Peek(11) == 0x342;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MLoad(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Dup2(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s65(s41, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 189
    * Starting at 0x1273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1284

    requires s0.stack[7] == 0xe67

    requires s0.stack[11] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0xe67;
      assert s1.Peek(12) == 0x342;
      var s2 := MStore(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MStore(s4);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x1284;
      assert s11.Peek(5) == 0xe67;
      assert s11.Peek(9) == 0x342;
      var s12 := Push2(s11, 0x10ab);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s66(s13, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 174
    * Starting at 0x10ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1284

    requires s0.stack[5] == 0xe67

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1284;
      assert s1.Peek(5) == 0xe67;
      assert s1.Peek(9) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x1284;
      assert s11.Peek(7) == 0xe67;
      assert s11.Peek(11) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x21f8a721);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x1284;
      assert s21.Peek(12) == 0xe67;
      assert s21.Peek(16) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x1284;
      assert s31.Peek(13) == 0xe67;
      assert s31.Peek(17) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s67(s41, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 175
    * Starting at 0x110e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xe67

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0xe67;
      assert s1.Peek(17) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s11, gas - 1)
      else
        ExecuteFromCFGNode_s68(s11, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 176
    * Starting at 0x111b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0xe67

    requires s0.stack[19] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1284;
      assert s1.Peek(16) == 0xe67;
      assert s1.Peek(20) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 69
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0xe67

    requires s0.stack[19] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1284;
      assert s1.Peek(15) == 0xe67;
      assert s1.Peek(19) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s71(s9, gas - 1)
      else
        ExecuteFromCFGNode_s70(s9, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0xe67

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1284;
      assert s1.Peek(11) == 0xe67;
      assert s1.Peek(15) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 71
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0xe67

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1284;
      assert s1.Peek(10) == 0xe67;
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x1284;
      assert s11.Peek(9) == 0xe67;
      assert s11.Peek(13) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s73(s14, gas - 1)
      else
        ExecuteFromCFGNode_s72(s14, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0xe67

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1284;
      assert s1.Peek(9) == 0xe67;
      assert s1.Peek(13) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 73
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0xe67

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0xe67;
      assert s1.Peek(12) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s8, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 190
    * Starting at 0x1284
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xe67

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xe67;
      assert s1.Peek(8) == 0x342;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x065e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s76(s8, gas - 1)
      else
        ExecuteFromCFGNode_s75(s8, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 191
    * Starting at 0x12a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe67

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xe67;
      assert s1.Peek(8) == 0x342;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0xe67;
      assert s11.Peek(9) == 0x342;
      var s12 := Push1(s11, 0x12);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(5) == 0xe67;
      assert s21.Peek(9) == 0x342;
      var s22 := Swap1(s21);
      var s23 := MLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := Swap1(s25);
      var s27 := Sub(s26);
      var s28 := Push1(s27, 0x64);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Revert(s30);
      // Segment is terminal (Revert, Stop or Return)
      s31
  }

  /** Node 76
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xe67

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xe67;
      assert s1.Peek(7) == 0x342;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s6, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 157
    * Starting at 0xe67
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe67 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0ed3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s79(s6, gas - 1)
      else
        ExecuteFromCFGNode_s78(s6, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 158
    * Starting at 0xe83
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xe83 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Dup1(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Dup2(s12);
      var s14 := Sub(s13);
      var s15 := Dup3(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x39);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x342;
      var s22 := Dup1(s21);
      var s23 := Push2(s22, 0x1530);
      var s24 := Push1(s23, 0x39);
      var s25 := Swap2(s24);
      var s26 := CodeCopy(s25);
      var s27 := Push1(s26, 0x40);
      var s28 := Add(s27);
      var s29 := Swap2(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(3) == 0x342;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Dup1(s33);
      var s35 := Swap2(s34);
      var s36 := Sub(s35);
      var s37 := Swap1(s36);
      var s38 := Revert(s37);
      // Segment is terminal (Revert, Stop or Return)
      s38
  }

  /** Node 79
    * Segment Id for this node is: 159
    * Starting at 0xed3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Push2(s1, 0x0902);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x902;
      assert s11.Peek(8) == 0x342;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Dup1(s16);
      var s18 := MLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x902;
      assert s21.Peek(9) == 0x342;
      var s22 := Swap1(s21);
      var s23 := Dup1(s22);
      var s24 := Dup4(s23);
      var s25 := Dup4(s24);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s80(s25, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 160
    * Starting at 0xef3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x902;
      assert s1.Peek(12) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0f30);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s6, gas - 1)
      else
        ExecuteFromCFGNode_s81(s6, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 161
    * Starting at 0xefc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xefc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x902;
      assert s1.Peek(13) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x902;
      assert s11.Peek(13) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0ef3);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s17, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 162
    * Starting at 0xf30
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf30 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x902;
      assert s1.Peek(12) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x902;
      assert s11.Peek(15) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x902;
      assert s21.Peek(17) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x902;
      assert s31.Peek(7) == 0x342;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s83(s41, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 163
    * Starting at 0xf5f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf5f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x902

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x902;
      assert s1.Peek(6) == 0x342;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x902;
      assert s11.Peek(5) == 0x342;
      var s12 := Keccak256(s11);
      var s13 := Dup3(s12);
      var s14 := Push2(s13, 0x148b);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s84(s15, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 204
    * Starting at 0x148b
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x148b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x902

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x902;
      assert s1.Peek(5) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Push32(s7, 0xca446dd900000000000000000000000000000000000000000000000000000000);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x04);
      assert s11.Peek(7) == 0x902;
      assert s11.Peek(10) == 0x342;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Dup7(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push20(s16, 0xffffffffffffffffffffffffffffffffffffffff);
      var s18 := Dup6(s17);
      var s19 := Dup2(s18);
      var s20 := And(s19);
      var s21 := Push1(s20, 0x24);
      assert s21.Peek(9) == 0x902;
      assert s21.Peek(12) == 0x342;
      var s22 := Dup4(s21);
      var s23 := Add(s22);
      var s24 := MStore(s23);
      var s25 := Swap2(s24);
      var s26 := MLoad(s25);
      var s27 := Push2(s26, 0x0100);
      var s28 := Swap1(s27);
      var s29 := Swap4(s28);
      var s30 := Div(s29);
      var s31 := Swap1(s30);
      assert s31.Peek(7) == 0x902;
      assert s31.Peek(10) == 0x342;
      var s32 := Swap2(s31);
      var s33 := And(s32);
      var s34 := Swap3(s33);
      var s35 := Push4(s34, 0xca446dd9);
      var s36 := Swap3(s35);
      var s37 := Push1(s36, 0x44);
      var s38 := Dup1(s37);
      var s39 := Dup5(s38);
      var s40 := Add(s39);
      var s41 := Swap4(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s85(s41, gas - 1)
  }

  /** Node 85
    * Segment Id for this node is: 205
    * Starting at 0x14f3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(10) == 0x902;
      assert s1.Peek(13) == 0x342;
      var s2 := Swap1(s1);
      var s3 := Sub(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Dup4(s5);
      var s7 := Dup8(s6);
      var s8 := Dup1(s7);
      var s9 := ExtCodeSize(s8);
      var s10 := IsZero(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(13) == 0x902;
      assert s11.Peek(16) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1382);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s14, gas - 1)
      else
        ExecuteFromCFGNode_s86(s14, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 206
    * Starting at 0x1503
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1503 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x902

    requires s0.stack[15] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x902;
      assert s1.Peek(16) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 87
    * Segment Id for this node is: 195
    * Starting at 0x1382
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1382 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x902

    requires s0.stack[15] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0x902;
      assert s1.Peek(15) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1396);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s9, gas - 1)
      else
        ExecuteFromCFGNode_s88(s9, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 196
    * Starting at 0x138d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x138d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x902

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x902;
      assert s1.Peek(10) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 89
    * Segment Id for this node is: 197
    * Starting at 0x1396
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x902

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x902;
      assert s1.Peek(9) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 122
    * Starting at 0x902
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x902 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s4, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 59
    * Starting at 0x342
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x342 as nat
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

  /** Node 92
    * Segment Id for this node is: 76
    * Starting at 0x42a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0288);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0440);
      assert s11.Peek(0) == 0x440;
      assert s11.Peek(4) == 0x288;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s94(s12, gas - 1)
      else
        ExecuteFromCFGNode_s93(s12, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 77
    * Starting at 0x43c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 94
    * Segment Id for this node is: 78
    * Starting at 0x440
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x440 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x288;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 5, 0x0100000000);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x288;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x045b);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s96(s15, gas - 1)
      else
        ExecuteFromCFGNode_s95(s15, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 79
    * Starting at 0x457
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x457 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 96
    * Segment Id for this node is: 80
    * Starting at 0x45b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x288;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x046d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s98(s11, gas - 1)
      else
        ExecuteFromCFGNode_s97(s11, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 81
    * Starting at 0x469
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x469 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 98
    * Segment Id for this node is: 82
    * Starting at 0x46d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x288;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0x288;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 5, 0x0100000000);
      var s16 := Dup4(s15);
      var s17 := Gt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x048f);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s100(s21, gas - 1)
      else
        ExecuteFromCFGNode_s99(s21, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 83
    * Starting at 0x48b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 100
    * Segment Id for this node is: 84
    * Starting at 0x48f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x288;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup1(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Div(s10);
      assert s11.Peek(8) == 0x288;
      var s12 := Mul(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0x288;
      var s22 := Dup1(s21);
      var s23 := Swap4(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x288;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      var s34 := Dup1(s33);
      var s35 := Dup3(s34);
      var s36 := Dup5(s35);
      var s37 := CallDataCopy(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s101(s41, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 85
    * Starting at 0x4bf
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4bf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(10) == 0x288;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0d14);
      var s9 := Swap5(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0xd14;
      assert s11.Peek(5) == 0x288;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s102(s15, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 148
    * Starting at 0xd14
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x065e);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x65e;
      assert s11.Peek(7) == 0x288;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Dup3(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(7) == 0x65e;
      assert s21.Peek(10) == 0x288;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup4(s24);
      var s26 := Dup4(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s103(s26, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 149
    * Starting at 0xd36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x288;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0d73);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s105(s6, gas - 1)
      else
        ExecuteFromCFGNode_s104(s6, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 150
    * Starting at 0xd3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x65e;
      assert s1.Peek(13) == 0x288;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x65e;
      assert s11.Peek(13) == 0x288;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0d36);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s103(s17, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 151
    * Starting at 0xd73
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x288;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x65e;
      assert s11.Peek(15) == 0x288;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x65e;
      assert s21.Peek(17) == 0x288;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x65e;
      assert s31.Peek(7) == 0x288;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s106(s41, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 152
    * Starting at 0xda2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x65e;
      assert s1.Peek(6) == 0x288;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x65e;
      assert s11.Peek(5) == 0x288;
      var s12 := Keccak256(s11);
      var s13 := Push2(s12, 0x1417);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s107(s14, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 201
    * Starting at 0x1417
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1417 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x65e

    requires s0.stack[4] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x65e;
      assert s1.Peek(4) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x65e;
      assert s11.Peek(6) == 0x288;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0xbd02d0f5);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x65e;
      assert s21.Peek(11) == 0x288;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x65e;
      assert s31.Peek(12) == 0x288;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s108(s41, gas - 1)
  }

  /** Node 108
    * Segment Id for this node is: 202
    * Starting at 0x147a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x65e

    requires s0.stack[11] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x288;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s110(s11, gas - 1)
      else
        ExecuteFromCFGNode_s109(s11, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 203
    * Starting at 0x1487
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1487 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x65e;
      assert s1.Peek(15) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 110
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x65e;
      assert s1.Peek(14) == 0x288;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s112(s9, gas - 1)
      else
        ExecuteFromCFGNode_s111(s9, gas - 1)
  }

  /** Node 111
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x65e;
      assert s1.Peek(10) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 112
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x65e;
      assert s1.Peek(9) == 0x288;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x65e;
      assert s11.Peek(8) == 0x288;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s14, gas - 1)
      else
        ExecuteFromCFGNode_s113(s14, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x65e;
      assert s1.Peek(8) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x65e;
      assert s1.Peek(7) == 0x288;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s8, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x288;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s6, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 75
    * Starting at 0x422
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x422 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f7);
      var s3 := Push2(s2, 0x0cd4);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s117(s4, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 147
    * Starting at 0xcd4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xcd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05b9);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x5b9;
      assert s11.Peek(4) == 0xf7;
      var s12 := Push1(s11, 0x19);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6f64652e726567697374726174696f6e2e656e61626c656400000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0664);
      assert s21.Peek(0) == 0x664;
      assert s21.Peek(2) == 0x5b9;
      assert s21.Peek(4) == 0xf7;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s22, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 105
    * Starting at 0x664
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x664 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5b9

    requires s0.stack[3] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b9;
      assert s1.Peek(3) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x065e);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x65e;
      assert s11.Peek(7) == 0x5b9;
      assert s11.Peek(9) == 0xf7;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Dup3(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(7) == 0x65e;
      assert s21.Peek(10) == 0x5b9;
      assert s21.Peek(12) == 0xf7;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup4(s24);
      var s26 := Dup4(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s119(s26, gas - 1)
  }

  /** Node 119
    * Segment Id for this node is: 106
    * Starting at 0x686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x5b9

    requires s0.stack[14] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x5b9;
      assert s1.Peek(14) == 0xf7;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x06c3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s121(s6, gas - 1)
      else
        ExecuteFromCFGNode_s120(s6, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 107
    * Starting at 0x68f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x5b9

    requires s0.stack[14] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x65e;
      assert s1.Peek(13) == 0x5b9;
      assert s1.Peek(15) == 0xf7;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x65e;
      assert s11.Peek(13) == 0x5b9;
      assert s11.Peek(15) == 0xf7;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0686);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s119(s17, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 108
    * Starting at 0x6c3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x5b9

    requires s0.stack[14] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x5b9;
      assert s1.Peek(14) == 0xf7;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x65e;
      assert s11.Peek(15) == 0x5b9;
      assert s11.Peek(17) == 0xf7;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x65e;
      assert s21.Peek(17) == 0x5b9;
      assert s21.Peek(19) == 0xf7;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x65e;
      assert s31.Peek(7) == 0x5b9;
      assert s31.Peek(9) == 0xf7;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s122(s41, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 109
    * Starting at 0x6f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x5b9

    requires s0.stack[9] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x65e;
      assert s1.Peek(6) == 0x5b9;
      assert s1.Peek(8) == 0xf7;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x65e;
      assert s11.Peek(5) == 0x5b9;
      assert s11.Peek(7) == 0xf7;
      var s12 := Keccak256(s11);
      var s13 := Push2(s12, 0x1151);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s14, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 182
    * Starting at 0x1151
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x65e

    requires s0.stack[4] == 0x5b9

    requires s0.stack[6] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x65e;
      assert s1.Peek(4) == 0x5b9;
      assert s1.Peek(6) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x65e;
      assert s11.Peek(6) == 0x5b9;
      assert s11.Peek(8) == 0xf7;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x7ae1cfca);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x65e;
      assert s21.Peek(11) == 0x5b9;
      assert s21.Peek(13) == 0xf7;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x65e;
      assert s31.Peek(12) == 0x5b9;
      assert s31.Peek(14) == 0xf7;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s124(s41, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 183
    * Starting at 0x11b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x65e

    requires s0.stack[11] == 0x5b9

    requires s0.stack[13] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x5b9;
      assert s1.Peek(14) == 0xf7;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s126(s11, gas - 1)
      else
        ExecuteFromCFGNode_s125(s11, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 184
    * Starting at 0x11c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x5b9

    requires s0.stack[16] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x65e;
      assert s1.Peek(15) == 0x5b9;
      assert s1.Peek(17) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 126
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x5b9

    requires s0.stack[16] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x65e;
      assert s1.Peek(14) == 0x5b9;
      assert s1.Peek(16) == 0xf7;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s128(s9, gas - 1)
      else
        ExecuteFromCFGNode_s127(s9, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x5b9

    requires s0.stack[11] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x65e;
      assert s1.Peek(10) == 0x5b9;
      assert s1.Peek(12) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 128
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x5b9

    requires s0.stack[11] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x65e;
      assert s1.Peek(9) == 0x5b9;
      assert s1.Peek(11) == 0xf7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x65e;
      assert s11.Peek(8) == 0x5b9;
      assert s11.Peek(10) == 0xf7;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s14, gas - 1)
      else
        ExecuteFromCFGNode_s129(s14, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x5b9

    requires s0.stack[9] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x65e;
      assert s1.Peek(8) == 0x5b9;
      assert s1.Peek(10) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 130
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x5b9

    requires s0.stack[9] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x65e;
      assert s1.Peek(7) == 0x5b9;
      assert s1.Peek(9) == 0xf7;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s8, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x5b9

    requires s0.stack[5] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b9;
      assert s1.Peek(5) == 0xf7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s6, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 98
    * Starting at 0x5b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf7;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s5, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 25
    * Starting at 0xf7
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Swap2(s4);
      var s6 := IsZero(s5);
      var s7 := IsZero(s6);
      var s8 := Dup3(s7);
      var s9 := MStore(s8);
      var s10 := MLoad(s9);
      var s11 := Swap1(s10);
      var s12 := Dup2(s11);
      var s13 := Swap1(s12);
      var s14 := Sub(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Return(s17);
      // Segment is terminal (Revert, Stop or Return)
      s18
  }

  /** Node 134
    * Segment Id for this node is: 10
    * Starting at 0x66
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x5e9d4044);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x036a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s157(s6, gas - 1)
      else
        ExecuteFromCFGNode_s135(s6, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 11
    * Starting at 0x72
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x72 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x6ada7847);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0412);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s155(s5, gas - 1)
      else
        ExecuteFromCFGNode_s136(s5, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 12
    * Starting at 0x7d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x6fdbe57b);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x041a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s138(s5, gas - 1)
      else
        ExecuteFromCFGNode_s137(s5, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 13
    * Starting at 0x88
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00ea);
      assert s1.Peek(0) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 74
    * Starting at 0x41a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0288);
      var s3 := Push2(s2, 0x0c94);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s4, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 146
    * Starting at 0xc94
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc94 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05b9);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x5b9;
      assert s11.Peek(4) == 0x288;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6f64652e7065722e6d696e69706f6f6c2e7374616b652e6d696e696d756d00);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d14);
      assert s21.Peek(0) == 0xd14;
      assert s21.Peek(2) == 0x5b9;
      assert s21.Peek(4) == 0x288;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s22, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 148
    * Starting at 0xd14
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd14 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[1] == 0x5b9

    requires s0.stack[3] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x5b9;
      assert s1.Peek(3) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x065e);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x65e;
      assert s11.Peek(7) == 0x5b9;
      assert s11.Peek(9) == 0x288;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Dup3(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(7) == 0x65e;
      assert s21.Peek(10) == 0x5b9;
      assert s21.Peek(12) == 0x288;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup4(s24);
      var s26 := Dup4(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s141(s26, gas - 1)
  }

  /** Node 141
    * Segment Id for this node is: 149
    * Starting at 0xd36
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd36 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x5b9

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x5b9;
      assert s1.Peek(14) == 0x288;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0d73);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s143(s6, gas - 1)
      else
        ExecuteFromCFGNode_s142(s6, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 150
    * Starting at 0xd3f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x5b9

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x65e;
      assert s1.Peek(13) == 0x5b9;
      assert s1.Peek(15) == 0x288;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x65e;
      assert s11.Peek(13) == 0x5b9;
      assert s11.Peek(15) == 0x288;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0d36);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s141(s17, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 151
    * Starting at 0xd73
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd73 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x5b9

    requires s0.stack[14] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x5b9;
      assert s1.Peek(14) == 0x288;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x65e;
      assert s11.Peek(15) == 0x5b9;
      assert s11.Peek(17) == 0x288;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x65e;
      assert s21.Peek(17) == 0x5b9;
      assert s21.Peek(19) == 0x288;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x65e;
      assert s31.Peek(7) == 0x5b9;
      assert s31.Peek(9) == 0x288;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s144(s41, gas - 1)
  }

  /** Node 144
    * Segment Id for this node is: 152
    * Starting at 0xda2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xda2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x5b9

    requires s0.stack[9] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x65e;
      assert s1.Peek(6) == 0x5b9;
      assert s1.Peek(8) == 0x288;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x65e;
      assert s11.Peek(5) == 0x5b9;
      assert s11.Peek(7) == 0x288;
      var s12 := Keccak256(s11);
      var s13 := Push2(s12, 0x1417);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s145(s14, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 201
    * Starting at 0x1417
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1417 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x65e

    requires s0.stack[4] == 0x5b9

    requires s0.stack[6] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x65e;
      assert s1.Peek(4) == 0x5b9;
      assert s1.Peek(6) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x65e;
      assert s11.Peek(6) == 0x5b9;
      assert s11.Peek(8) == 0x288;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0xbd02d0f5);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x65e;
      assert s21.Peek(11) == 0x5b9;
      assert s21.Peek(13) == 0x288;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x65e;
      assert s31.Peek(12) == 0x5b9;
      assert s31.Peek(14) == 0x288;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s146(s41, gas - 1)
  }

  /** Node 146
    * Segment Id for this node is: 202
    * Starting at 0x147a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x147a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[8] == 0x65e

    requires s0.stack[11] == 0x5b9

    requires s0.stack[13] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x5b9;
      assert s1.Peek(14) == 0x288;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s148(s11, gas - 1)
      else
        ExecuteFromCFGNode_s147(s11, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 203
    * Starting at 0x1487
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1487 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x5b9

    requires s0.stack[16] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x65e;
      assert s1.Peek(15) == 0x5b9;
      assert s1.Peek(17) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 148
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x5b9

    requires s0.stack[16] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x65e;
      assert s1.Peek(14) == 0x5b9;
      assert s1.Peek(16) == 0x288;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s150(s9, gas - 1)
      else
        ExecuteFromCFGNode_s149(s9, gas - 1)
  }

  /** Node 149
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x5b9

    requires s0.stack[11] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x65e;
      assert s1.Peek(10) == 0x5b9;
      assert s1.Peek(12) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 150
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x5b9

    requires s0.stack[11] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x65e;
      assert s1.Peek(9) == 0x5b9;
      assert s1.Peek(11) == 0x288;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x65e;
      assert s11.Peek(8) == 0x5b9;
      assert s11.Peek(10) == 0x288;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s152(s14, gas - 1)
      else
        ExecuteFromCFGNode_s151(s14, gas - 1)
  }

  /** Node 151
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x5b9

    requires s0.stack[9] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x65e;
      assert s1.Peek(8) == 0x5b9;
      assert s1.Peek(10) == 0x288;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 152
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x5b9

    requires s0.stack[9] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x65e;
      assert s1.Peek(7) == 0x5b9;
      assert s1.Peek(9) == 0x288;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s153(s8, gas - 1)
  }

  /** Node 153
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[3] == 0x5b9

    requires s0.stack[5] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x5b9;
      assert s1.Peek(5) == 0x288;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s154(s6, gas - 1)
  }

  /** Node 154
    * Segment Id for this node is: 98
    * Starting at 0x5b9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s154(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x288;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s38(s5, gas - 1)
  }

  /** Node 155
    * Segment Id for this node is: 73
    * Starting at 0x412
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s155(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x412 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f7);
      var s3 := Push2(s2, 0x0c54);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s156(s4, gas - 1)
  }

  /** Node 156
    * Segment Id for this node is: 145
    * Starting at 0xc54
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s156(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05b9);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x5b9;
      assert s11.Peek(4) == 0xf7;
      var s12 := Push1(s11, 0x14);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6f64652e6465706f7369742e656e61626c6564000000000000000000000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0664);
      assert s21.Peek(0) == 0x664;
      assert s21.Peek(2) == 0x5b9;
      assert s21.Peek(4) == 0xf7;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s22, gas - 1)
  }

  /** Node 157
    * Segment Id for this node is: 63
    * Starting at 0x36a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s157(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0342);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0380);
      assert s11.Peek(0) == 0x380;
      assert s11.Peek(4) == 0x342;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s159(s12, gas - 1)
      else
        ExecuteFromCFGNode_s158(s12, gas - 1)
  }

  /** Node 158
    * Segment Id for this node is: 64
    * Starting at 0x37c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s158(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x37c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 159
    * Segment Id for this node is: 65
    * Starting at 0x380
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s159(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x380 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 5, 0x0100000000);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x342;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x039b);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s161(s15, gas - 1)
      else
        ExecuteFromCFGNode_s160(s15, gas - 1)
  }

  /** Node 160
    * Segment Id for this node is: 66
    * Starting at 0x397
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s160(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x397 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 161
    * Segment Id for this node is: 67
    * Starting at 0x39b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s161(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x39b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x03ad);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s163(s11, gas - 1)
      else
        ExecuteFromCFGNode_s162(s11, gas - 1)
  }

  /** Node 162
    * Segment Id for this node is: 68
    * Starting at 0x3a9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s162(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 163
    * Segment Id for this node is: 69
    * Starting at 0x3ad
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s163(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ad as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0x342;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 5, 0x0100000000);
      var s16 := Dup4(s15);
      var s17 := Gt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x03cf);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s165(s21, gas - 1)
      else
        ExecuteFromCFGNode_s164(s21, gas - 1)
  }

  /** Node 164
    * Segment Id for this node is: 70
    * Starting at 0x3cb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s164(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 165
    * Segment Id for this node is: 71
    * Starting at 0x3cf
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s165(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x342;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup1(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Div(s10);
      assert s11.Peek(8) == 0x342;
      var s12 := Mul(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0x342;
      var s22 := Dup1(s21);
      var s23 := Swap4(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x342;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      var s34 := Dup1(s33);
      var s35 := Dup3(s34);
      var s36 := Dup5(s35);
      var s37 := CallDataCopy(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s166(s41, gas - 1)
  }

  /** Node 166
    * Segment Id for this node is: 72
    * Starting at 0x3ff
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s166(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(10) == 0x342;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Swap2(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(5) == 0x342;
      var s12 := Pop(s11);
      var s13 := Push2(s12, 0x094f);
      var s14 := Swap2(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s167(s17, gas - 1)
  }

  /** Node 167
    * Segment Id for this node is: 125
    * Starting at 0x94f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s167(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x94f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Push2(s1, 0x09a8);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x9a8;
      assert s11.Peek(8) == 0x342;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Dup1(s14);
      var s16 := Push32(s15, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x08);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x9a8;
      assert s21.Peek(6) == 0x342;
      var s22 := Swap2(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Dup2(s27);
      var s29 := Dup4(s28);
      var s30 := Sub(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x9a8;
      assert s31.Peek(6) == 0x342;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MStore(s35);
      var s37 := Dup1(s36);
      var s38 := MLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s168(s41, gas - 1)
  }

  /** Node 168
    * Segment Id for this node is: 126
    * Starting at 0x9a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s168(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x9a8

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.Peek(1) == 0x9a8;
      assert s1.Peek(4) == 0x342;
      var s2 := Push2(s1, 0x1151);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s169(s3, gas - 1)
  }

  /** Node 169
    * Segment Id for this node is: 182
    * Starting at 0x1151
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s169(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x9a8

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x9a8;
      assert s1.Peek(4) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x9a8;
      assert s11.Peek(6) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x7ae1cfca);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x9a8;
      assert s21.Peek(11) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x9a8;
      assert s31.Peek(12) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s170(s41, gas - 1)
  }

  /** Node 170
    * Segment Id for this node is: 183
    * Starting at 0x11b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s170(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x9a8

    requires s0.stack[11] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x9a8;
      assert s1.Peek(12) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s172(s11, gas - 1)
      else
        ExecuteFromCFGNode_s171(s11, gas - 1)
  }

  /** Node 171
    * Segment Id for this node is: 184
    * Starting at 0x11c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s171(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x9a8

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x9a8;
      assert s1.Peek(15) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 172
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s172(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x9a8

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x9a8;
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s174(s9, gas - 1)
      else
        ExecuteFromCFGNode_s173(s9, gas - 1)
  }

  /** Node 173
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s173(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x9a8

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x9a8;
      assert s1.Peek(10) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 174
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s174(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x9a8

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x9a8;
      assert s1.Peek(9) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x9a8;
      assert s11.Peek(8) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s176(s14, gas - 1)
      else
        ExecuteFromCFGNode_s175(s14, gas - 1)
  }

  /** Node 175
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s175(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9a8

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x9a8;
      assert s1.Peek(8) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 176
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s176(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x9a8

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x9a8;
      assert s1.Peek(7) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s177(s8, gas - 1)
  }

  /** Node 177
    * Segment Id for this node is: 127
    * Starting at 0x9a8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s177(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9a8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0a6e);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s4, gas - 1)
      else
        ExecuteFromCFGNode_s178(s4, gas - 1)
  }

  /** Node 178
    * Segment Id for this node is: 128
    * Starting at 0x9ae
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s178(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x0a02);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0xa02;
      assert s11.Peek(5) == 0x342;
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
      assert s21.Peek(1) == 0xa02;
      assert s21.Peek(5) == 0x342;
      var s22 := Push2(s21, 0x11c5);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s179(s23, gas - 1)
  }

  /** Node 179
    * Segment Id for this node is: 185
    * Starting at 0x11c5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s179(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0xa02

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xa02;
      assert s1.Peek(5) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1284);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x1284;
      assert s11.Peek(8) == 0xa02;
      assert s11.Peek(12) == 0x342;
      var s12 := Push32(s11, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x10);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x1284;
      assert s21.Peek(9) == 0xa02;
      assert s21.Peek(13) == 0x342;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup1(s24);
      var s26 := Dup4(s25);
      var s27 := Dup4(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s180(s27, gas - 1)
  }

  /** Node 180
    * Segment Id for this node is: 186
    * Starting at 0x1207
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s180(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xa02

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0xa02;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x1244);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s182(s6, gas - 1)
      else
        ExecuteFromCFGNode_s181(s6, gas - 1)
  }

  /** Node 181
    * Segment Id for this node is: 187
    * Starting at 0x1210
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s181(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xa02

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0xa02;
      assert s1.Peek(17) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0x1284;
      assert s11.Peek(13) == 0xa02;
      assert s11.Peek(17) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x1207);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s180(s17, gas - 1)
  }

  /** Node 182
    * Segment Id for this node is: 188
    * Starting at 0x1244
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s182(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xa02

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0xa02;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x1284;
      assert s11.Peek(15) == 0xa02;
      assert s11.Peek(19) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(13) == 0x1284;
      assert s21.Peek(17) == 0xa02;
      assert s21.Peek(21) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x1284;
      assert s31.Peek(7) == 0xa02;
      assert s31.Peek(11) == 0x342;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MLoad(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Dup2(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s183(s41, gas - 1)
  }

  /** Node 183
    * Segment Id for this node is: 189
    * Starting at 0x1273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s183(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1284

    requires s0.stack[7] == 0xa02

    requires s0.stack[11] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0xa02;
      assert s1.Peek(12) == 0x342;
      var s2 := MStore(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MStore(s4);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x1284;
      assert s11.Peek(5) == 0xa02;
      assert s11.Peek(9) == 0x342;
      var s12 := Push2(s11, 0x10ab);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s184(s13, gas - 1)
  }

  /** Node 184
    * Segment Id for this node is: 174
    * Starting at 0x10ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s184(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1284

    requires s0.stack[5] == 0xa02

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1284;
      assert s1.Peek(5) == 0xa02;
      assert s1.Peek(9) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x1284;
      assert s11.Peek(7) == 0xa02;
      assert s11.Peek(11) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x21f8a721);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x1284;
      assert s21.Peek(12) == 0xa02;
      assert s21.Peek(16) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x1284;
      assert s31.Peek(13) == 0xa02;
      assert s31.Peek(17) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s185(s41, gas - 1)
  }

  /** Node 185
    * Segment Id for this node is: 175
    * Starting at 0x110e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s185(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xa02

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0xa02;
      assert s1.Peek(17) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s187(s11, gas - 1)
      else
        ExecuteFromCFGNode_s186(s11, gas - 1)
  }

  /** Node 186
    * Segment Id for this node is: 176
    * Starting at 0x111b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s186(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0xa02

    requires s0.stack[19] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1284;
      assert s1.Peek(16) == 0xa02;
      assert s1.Peek(20) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 187
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s187(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0xa02

    requires s0.stack[19] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1284;
      assert s1.Peek(15) == 0xa02;
      assert s1.Peek(19) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s189(s9, gas - 1)
      else
        ExecuteFromCFGNode_s188(s9, gas - 1)
  }

  /** Node 188
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s188(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0xa02

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1284;
      assert s1.Peek(11) == 0xa02;
      assert s1.Peek(15) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 189
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s189(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0xa02

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1284;
      assert s1.Peek(10) == 0xa02;
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x1284;
      assert s11.Peek(9) == 0xa02;
      assert s11.Peek(13) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s191(s14, gas - 1)
      else
        ExecuteFromCFGNode_s190(s14, gas - 1)
  }

  /** Node 190
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s190(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0xa02

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1284;
      assert s1.Peek(9) == 0xa02;
      assert s1.Peek(13) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 191
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s191(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0xa02

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0xa02;
      assert s1.Peek(12) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s192(s8, gas - 1)
  }

  /** Node 192
    * Segment Id for this node is: 190
    * Starting at 0x1284
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s192(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xa02

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xa02;
      assert s1.Peek(8) == 0x342;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x065e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s194(s8, gas - 1)
      else
        ExecuteFromCFGNode_s193(s8, gas - 1)
  }

  /** Node 193
    * Segment Id for this node is: 191
    * Starting at 0x12a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s193(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xa02

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xa02;
      assert s1.Peek(8) == 0x342;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0xa02;
      assert s11.Peek(9) == 0x342;
      var s12 := Push1(s11, 0x12);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(5) == 0xa02;
      assert s21.Peek(9) == 0x342;
      var s22 := Swap1(s21);
      var s23 := MLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := Swap1(s25);
      var s27 := Sub(s26);
      var s28 := Push1(s27, 0x64);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Revert(s30);
      // Segment is terminal (Revert, Stop or Return)
      s31
  }

  /** Node 194
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s194(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0xa02

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xa02;
      assert s1.Peek(7) == 0x342;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s195(s6, gas - 1)
  }

  /** Node 195
    * Segment Id for this node is: 129
    * Starting at 0xa02
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s195(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa02 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0a6e);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s197(s6, gas - 1)
      else
        ExecuteFromCFGNode_s196(s6, gas - 1)
  }

  /** Node 196
    * Segment Id for this node is: 130
    * Starting at 0xa1e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s196(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa1e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Dup1(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Dup2(s12);
      var s14 := Sub(s13);
      var s15 := Dup3(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x39);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x342;
      var s22 := Dup1(s21);
      var s23 := Push2(s22, 0x1530);
      var s24 := Push1(s23, 0x39);
      var s25 := Swap2(s24);
      var s26 := CodeCopy(s25);
      var s27 := Push1(s26, 0x40);
      var s28 := Add(s27);
      var s29 := Swap2(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(3) == 0x342;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Dup1(s33);
      var s35 := Swap2(s34);
      var s36 := Sub(s35);
      var s37 := Swap1(s36);
      var s38 := Revert(s37);
      // Segment is terminal (Revert, Stop or Return)
      s38
  }

  /** Node 197
    * Segment Id for this node is: 131
    * Starting at 0xa6e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s197(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa6e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
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
      assert s11.Peek(4) == 0x342;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup1(s12);
      var s14 := MLoad(s13);
      var s15 := Dup1(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Swap2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x1f);
      assert s21.Peek(6) == 0x342;
      var s22 := Dup2(s21);
      var s23 := MStore(s22);
      var s24 := Push32(s23, 0x6e6f64652e766f74696e672e706f7765722e7374616b652e6d6178696d756d00);
      var s25 := Swap3(s24);
      var s26 := Add(s25);
      var s27 := Swap2(s26);
      var s28 := Swap1(s27);
      var s29 := Swap2(s28);
      var s30 := MStore(s29);
      var s31 := Push32(s30, 0x1b6028195e85a43527189139611db98fd210d645ea6839e6c06effd45b5934a9);
      assert s31.Peek(4) == 0x342;
      var s32 := Dup2(s31);
      var s33 := Eq(s32);
      var s34 := IsZero(s33);
      var s35 := Push2(s34, 0x0bb0);
      var s36 := JumpI(s35);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s35.stack[1] > 0 then
        ExecuteFromCFGNode_s221(s36, gas - 1)
      else
        ExecuteFromCFGNode_s198(s36, gas - 1)
  }

  /** Node 198
    * Segment Id for this node is: 132
    * Starting at 0xad7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s198(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xad7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x342;
      var s2 := Push2(s1, 0x0b16);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := MStore(s8);
      var s10 := Dup1(s9);
      var s11 := Push1(s10, 0x16);
      assert s11.Peek(3) == 0xb16;
      assert s11.Peek(8) == 0x342;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Push32(s15, 0x726f636b65744e6574776f726b536e617073686f747300000000000000000000);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := Push2(s19, 0x11c5);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s199(s21, gas - 1)
  }

  /** Node 199
    * Segment Id for this node is: 185
    * Starting at 0x11c5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s199(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0xb16

    requires s0.stack[6] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xb16;
      assert s1.Peek(6) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1284);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x1284;
      assert s11.Peek(8) == 0xb16;
      assert s11.Peek(13) == 0x342;
      var s12 := Push32(s11, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x10);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x1284;
      assert s21.Peek(9) == 0xb16;
      assert s21.Peek(14) == 0x342;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup1(s24);
      var s26 := Dup4(s25);
      var s27 := Dup4(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s200(s27, gas - 1)
  }

  /** Node 200
    * Segment Id for this node is: 186
    * Starting at 0x1207
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s200(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xb16

    requires s0.stack[17] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0xb16;
      assert s1.Peek(17) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x1244);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s202(s6, gas - 1)
      else
        ExecuteFromCFGNode_s201(s6, gas - 1)
  }

  /** Node 201
    * Segment Id for this node is: 187
    * Starting at 0x1210
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s201(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xb16

    requires s0.stack[17] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0xb16;
      assert s1.Peek(18) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0x1284;
      assert s11.Peek(13) == 0xb16;
      assert s11.Peek(18) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x1207);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s200(s17, gas - 1)
  }

  /** Node 202
    * Segment Id for this node is: 188
    * Starting at 0x1244
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s202(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xb16

    requires s0.stack[17] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0xb16;
      assert s1.Peek(17) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x1284;
      assert s11.Peek(15) == 0xb16;
      assert s11.Peek(20) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(13) == 0x1284;
      assert s21.Peek(17) == 0xb16;
      assert s21.Peek(22) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x1284;
      assert s31.Peek(7) == 0xb16;
      assert s31.Peek(12) == 0x342;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MLoad(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Dup2(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s203(s41, gas - 1)
  }

  /** Node 203
    * Segment Id for this node is: 189
    * Starting at 0x1273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s203(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[3] == 0x1284

    requires s0.stack[7] == 0xb16

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0xb16;
      assert s1.Peek(13) == 0x342;
      var s2 := MStore(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MStore(s4);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x1284;
      assert s11.Peek(5) == 0xb16;
      assert s11.Peek(10) == 0x342;
      var s12 := Push2(s11, 0x10ab);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s204(s13, gas - 1)
  }

  /** Node 204
    * Segment Id for this node is: 174
    * Starting at 0x10ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s204(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x1284

    requires s0.stack[5] == 0xb16

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1284;
      assert s1.Peek(5) == 0xb16;
      assert s1.Peek(10) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x1284;
      assert s11.Peek(7) == 0xb16;
      assert s11.Peek(12) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x21f8a721);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x1284;
      assert s21.Peek(12) == 0xb16;
      assert s21.Peek(17) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x1284;
      assert s31.Peek(13) == 0xb16;
      assert s31.Peek(18) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s205(s41, gas - 1)
  }

  /** Node 205
    * Segment Id for this node is: 175
    * Starting at 0x110e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s205(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0xb16

    requires s0.stack[17] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0xb16;
      assert s1.Peek(18) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s207(s11, gas - 1)
      else
        ExecuteFromCFGNode_s206(s11, gas - 1)
  }

  /** Node 206
    * Segment Id for this node is: 176
    * Starting at 0x111b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s206(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0xb16

    requires s0.stack[20] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1284;
      assert s1.Peek(16) == 0xb16;
      assert s1.Peek(21) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 207
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s207(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0xb16

    requires s0.stack[20] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1284;
      assert s1.Peek(15) == 0xb16;
      assert s1.Peek(20) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s209(s9, gas - 1)
      else
        ExecuteFromCFGNode_s208(s9, gas - 1)
  }

  /** Node 208
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s208(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0xb16

    requires s0.stack[15] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1284;
      assert s1.Peek(11) == 0xb16;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 209
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s209(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0xb16

    requires s0.stack[15] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1284;
      assert s1.Peek(10) == 0xb16;
      assert s1.Peek(15) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x1284;
      assert s11.Peek(9) == 0xb16;
      assert s11.Peek(14) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s211(s14, gas - 1)
      else
        ExecuteFromCFGNode_s210(s14, gas - 1)
  }

  /** Node 210
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s210(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0xb16

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1284;
      assert s1.Peek(9) == 0xb16;
      assert s1.Peek(14) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 211
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s211(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0xb16

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0xb16;
      assert s1.Peek(13) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s212(s8, gas - 1)
  }

  /** Node 212
    * Segment Id for this node is: 190
    * Starting at 0x1284
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s212(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[4] == 0xb16

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xb16;
      assert s1.Peek(9) == 0x342;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x065e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s214(s8, gas - 1)
      else
        ExecuteFromCFGNode_s213(s8, gas - 1)
  }

  /** Node 213
    * Segment Id for this node is: 191
    * Starting at 0x12a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s213(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xb16

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0xb16;
      assert s1.Peek(9) == 0x342;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0xb16;
      assert s11.Peek(10) == 0x342;
      var s12 := Push1(s11, 0x12);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(5) == 0xb16;
      assert s21.Peek(10) == 0x342;
      var s22 := Swap1(s21);
      var s23 := MLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := Swap1(s25);
      var s27 := Sub(s26);
      var s28 := Push1(s27, 0x64);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Revert(s30);
      // Segment is terminal (Revert, Stop or Return)
      s31
  }

  /** Node 214
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s214(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0xb16

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xb16;
      assert s1.Peek(8) == 0x342;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s215(s6, gas - 1)
  }

  /** Node 215
    * Segment Id for this node is: 133
    * Starting at 0xb16
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s215(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb16 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x342;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := And(s5);
      var s7 := Push4(s6, 0x5ba59649);
      var s8 := Dup4(s7);
      var s9 := Dup6(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MLoad(s10);
      assert s11.Peek(9) == 0x342;
      var s12 := Dup4(s11);
      var s13 := Push4(s12, 0xffffffff);
      var s14 := And(s13);
      var s15 := Push1(s14, 0xe0);
      var s16 := Shl(s15);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Push1(s18, 0x04);
      var s20 := Add(s19);
      var s21 := Dup1(s20);
      assert s21.Peek(10) == 0x342;
      var s22 := Dup4(s21);
      var s23 := Dup2(s22);
      var s24 := MStore(s23);
      var s25 := Push1(s24, 0x20);
      var s26 := Add(s25);
      var s27 := Dup3(s26);
      var s28 := PushN(s27, 28, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s29 := And(s28);
      var s30 := Dup2(s29);
      var s31 := MStore(s30);
      assert s31.Peek(10) == 0x342;
      var s32 := Push1(s31, 0x20);
      var s33 := Add(s32);
      var s34 := Swap3(s33);
      var s35 := Pop(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s216(s41, gas - 1)
  }

  /** Node 216
    * Segment Id for this node is: 134
    * Starting at 0xb7e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s216(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb7e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(11) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := Dup8(s4);
      var s6 := Dup1(s5);
      var s7 := ExtCodeSize(s6);
      var s8 := IsZero(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0b91);
      assert s11.Peek(0) == 0xb91;
      assert s11.Peek(16) == 0x342;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s218(s12, gas - 1)
      else
        ExecuteFromCFGNode_s217(s12, gas - 1)
  }

  /** Node 217
    * Segment Id for this node is: 135
    * Starting at 0xb8d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s217(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb8d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(15) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 218
    * Segment Id for this node is: 136
    * Starting at 0xb91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s218(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x0ba5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s220(s9, gas - 1)
      else
        ExecuteFromCFGNode_s219(s9, gas - 1)
  }

  /** Node 219
    * Segment Id for this node is: 137
    * Starting at 0xb9c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s219(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 220
    * Segment Id for this node is: 138
    * Starting at 0xba5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s220(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xba5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0902);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s9, gas - 1)
  }

  /** Node 221
    * Segment Id for this node is: 139
    * Starting at 0xbb0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s221(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbb0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := Push2(s1, 0x0c4f);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup5(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0xc4f;
      assert s11.Peek(9) == 0x342;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Dup1(s16);
      var s18 := MLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0xc4f;
      assert s21.Peek(10) == 0x342;
      var s22 := Swap1(s21);
      var s23 := Dup1(s22);
      var s24 := Dup4(s23);
      var s25 := Dup4(s24);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s222(s25, gas - 1)
  }

  /** Node 222
    * Segment Id for this node is: 140
    * Starting at 0xbd0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s222(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[9] == 0xc4f

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xc4f;
      assert s1.Peek(13) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x0c0d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s224(s6, gas - 1)
      else
        ExecuteFromCFGNode_s223(s6, gas - 1)
  }

  /** Node 223
    * Segment Id for this node is: 141
    * Starting at 0xbd9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s223(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xbd9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[9] == 0xc4f

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0xc4f;
      assert s1.Peek(14) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0xc4f;
      assert s11.Peek(14) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0bd0);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s222(s17, gas - 1)
  }

  /** Node 224
    * Segment Id for this node is: 142
    * Starting at 0xc0d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s224(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc0d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[9] == 0xc4f

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0xc4f;
      assert s1.Peek(13) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0xc4f;
      assert s11.Peek(16) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0xc4f;
      assert s21.Peek(18) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0xc4f;
      assert s31.Peek(8) == 0x342;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s225(s41, gas - 1)
  }

  /** Node 225
    * Segment Id for this node is: 143
    * Starting at 0xc3c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s225(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc3c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0xc4f

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0xc4f;
      assert s1.Peek(7) == 0x342;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0xc4f;
      assert s11.Peek(6) == 0x342;
      var s12 := Keccak256(s11);
      var s13 := Dup4(s12);
      var s14 := Push2(s13, 0x139e);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s226(s15, gas - 1)
  }

  /** Node 226
    * Segment Id for this node is: 198
    * Starting at 0x139e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s226(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x139e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0xc4f

    requires s0.stack[6] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xc4f;
      assert s1.Peek(6) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Push32(s7, 0xe2a4853a00000000000000000000000000000000000000000000000000000000);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x04);
      assert s11.Peek(7) == 0xc4f;
      assert s11.Peek(11) == 0x342;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Dup7(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x24);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Dup6(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(8) == 0xc4f;
      assert s21.Peek(12) == 0x342;
      var s22 := MStore(s21);
      var s23 := Swap1(s22);
      var s24 := MLoad(s23);
      var s25 := Push2(s24, 0x0100);
      var s26 := Swap1(s25);
      var s27 := Swap3(s26);
      var s28 := Div(s27);
      var s29 := Push20(s28, 0xffffffffffffffffffffffffffffffffffffffff);
      var s30 := And(s29);
      var s31 := Swap3(s30);
      assert s31.Peek(6) == 0xc4f;
      assert s31.Peek(10) == 0x342;
      var s32 := Push4(s31, 0xe2a4853a);
      var s33 := Swap3(s32);
      var s34 := Push1(s33, 0x44);
      var s35 := Dup1(s34);
      var s36 := Dup5(s35);
      var s37 := Add(s36);
      var s38 := Swap4(s37);
      var s39 := Dup3(s38);
      var s40 := Swap1(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s227(s41, gas - 1)
  }

  /** Node 227
    * Segment Id for this node is: 199
    * Starting at 0x1406
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s227(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1406 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[9] == 0xc4f

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Add(s0);
      assert s1.Peek(8) == 0xc4f;
      assert s1.Peek(12) == 0x342;
      var s2 := Dup2(s1);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x1382);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s229(s11, gas - 1)
      else
        ExecuteFromCFGNode_s228(s11, gas - 1)
  }

  /** Node 228
    * Segment Id for this node is: 200
    * Starting at 0x1413
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s228(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1413 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[12] == 0xc4f

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0xc4f;
      assert s1.Peek(17) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 229
    * Segment Id for this node is: 195
    * Starting at 0x1382
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s229(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1382 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[12] == 0xc4f

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(12) == 0xc4f;
      assert s1.Peek(16) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := Call(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1396);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s231(s9, gas - 1)
      else
        ExecuteFromCFGNode_s230(s9, gas - 1)
  }

  /** Node 230
    * Segment Id for this node is: 196
    * Starting at 0x138d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s230(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x138d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0xc4f

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0xc4f;
      assert s1.Peek(11) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 231
    * Segment Id for this node is: 197
    * Starting at 0x1396
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s231(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1396 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[6] == 0xc4f

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xc4f;
      assert s1.Peek(10) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s232(s8, gas - 1)
  }

  /** Node 232
    * Segment Id for this node is: 144
    * Starting at 0xc4f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s232(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s5, gas - 1)
  }

  /** Node 233
    * Segment Id for this node is: 14
    * Starting at 0x8c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s233(s0: EState, gas: nat): (s': EState)
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
      var s3 := Push4(s2, 0x1e72ba86);
      var s4 := Gt(s3);
      var s5 := Push2(s4, 0x00c8);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s294(s6, gas - 1)
      else
        ExecuteFromCFGNode_s234(s6, gas - 1)
  }

  /** Node 234
    * Segment Id for this node is: 15
    * Starting at 0x98
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s234(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x98 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1e72ba86);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0280);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s292(s5, gas - 1)
      else
        ExecuteFromCFGNode_s235(s5, gas - 1)
  }

  /** Node 235
    * Segment Id for this node is: 16
    * Starting at 0xa3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s235(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x2a57d018);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x029a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s244(s5, gas - 1)
      else
        ExecuteFromCFGNode_s236(s5, gas - 1)
  }

  /** Node 236
    * Segment Id for this node is: 17
    * Starting at 0xae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s236(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x46faa236);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0344);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s242(s5, gas - 1)
      else
        ExecuteFromCFGNode_s237(s5, gas - 1)
  }

  /** Node 237
    * Segment Id for this node is: 18
    * Starting at 0xb9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s237(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xb9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x54fd4d50);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x034c);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s239(s5, gas - 1)
      else
        ExecuteFromCFGNode_s238(s5, gas - 1)
  }

  /** Node 238
    * Segment Id for this node is: 19
    * Starting at 0xc4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s238(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x00ea);
      assert s1.Peek(0) == 0xea;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s2, gas - 1)
  }

  /** Node 239
    * Segment Id for this node is: 61
    * Starting at 0x34c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s239(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x34c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0354);
      var s3 := Push2(s2, 0x0946);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s240(s4, gas - 1)
  }

  /** Node 240
    * Segment Id for this node is: 124
    * Starting at 0x946
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s240(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x946 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x354

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x354;
      var s2 := Push1(s1, 0x00);
      var s3 := SLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := And(s4);
      var s6 := Dup2(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s241(s7, gas - 1)
  }

  /** Node 241
    * Segment Id for this node is: 62
    * Starting at 0x354
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s241(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x354 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x354

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x354;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push1(s4, 0xff);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := And(s7);
      var s9 := Dup3(s8);
      var s10 := MStore(s9);
      var s11 := MLoad(s10);
      assert s11.Peek(2) == 0x354;
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := Sub(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 242
    * Segment Id for this node is: 60
    * Starting at 0x344
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s242(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x344 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f7);
      var s3 := Push2(s2, 0x0906);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s243(s4, gas - 1)
  }

  /** Node 243
    * Segment Id for this node is: 123
    * Starting at 0x906
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s243(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x906 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05b9);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x5b9;
      assert s11.Peek(4) == 0xf7;
      var s12 := Push1(s11, 0x1d);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6f64652e766163616e742e6d696e69706f6f6c732e656e61626c6564000000);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0664);
      assert s21.Peek(0) == 0x664;
      assert s21.Peek(2) == 0x5b9;
      assert s21.Peek(4) == 0xf7;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s22, gas - 1)
  }

  /** Node 244
    * Segment Id for this node is: 49
    * Starting at 0x29a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s244(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0342);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x02b0);
      assert s11.Peek(0) == 0x2b0;
      assert s11.Peek(4) == 0x342;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s246(s12, gas - 1)
      else
        ExecuteFromCFGNode_s245(s12, gas - 1)
  }

  /** Node 245
    * Segment Id for this node is: 50
    * Starting at 0x2ac
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s245(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ac as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 246
    * Segment Id for this node is: 51
    * Starting at 0x2b0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s246(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 5, 0x0100000000);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x342;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x02cb);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s248(s15, gas - 1)
      else
        ExecuteFromCFGNode_s247(s15, gas - 1)
  }

  /** Node 247
    * Segment Id for this node is: 52
    * Starting at 0x2c7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s247(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 248
    * Segment Id for this node is: 53
    * Starting at 0x2cb
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s248(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x02dd);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s250(s11, gas - 1)
      else
        ExecuteFromCFGNode_s249(s11, gas - 1)
  }

  /** Node 249
    * Segment Id for this node is: 54
    * Starting at 0x2d9
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s249(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 250
    * Segment Id for this node is: 55
    * Starting at 0x2dd
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s250(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2dd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0x342;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 5, 0x0100000000);
      var s16 := Dup4(s15);
      var s17 := Gt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x02ff);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s252(s21, gas - 1)
      else
        ExecuteFromCFGNode_s251(s21, gas - 1)
  }

  /** Node 251
    * Segment Id for this node is: 56
    * Starting at 0x2fb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s251(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 252
    * Segment Id for this node is: 57
    * Starting at 0x2ff
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s252(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x342;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup1(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Div(s10);
      assert s11.Peek(8) == 0x342;
      var s12 := Mul(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0x342;
      var s22 := Dup1(s21);
      var s23 := Swap4(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x342;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      var s34 := Dup1(s33);
      var s35 := Dup3(s34);
      var s36 := Dup5(s35);
      var s37 := CallDataCopy(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s253(s41, gas - 1)
  }

  /** Node 253
    * Segment Id for this node is: 58
    * Starting at 0x32f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -8
    * Net Capacity Effect: +8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s253(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x32f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(10) == 0x342;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := CallDataLoad(s10);
      assert s11.Peek(3) == 0x342;
      var s12 := IsZero(s11);
      var s13 := IsZero(s12);
      var s14 := Swap1(s13);
      var s15 := Pop(s14);
      var s16 := Push2(s15, 0x0744);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s254(s17, gas - 1)
  }

  /** Node 254
    * Segment Id for this node is: 111
    * Starting at 0x744
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 7
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s254(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x744 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Push2(s1, 0x079d);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Add(s7);
      var s9 := Dup1(s8);
      var s10 := Dup3(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x79d;
      assert s11.Peek(8) == 0x342;
      var s12 := MStore(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Dup1(s14);
      var s16 := Push32(s15, 0x6465706c6f796564000000000000000000000000000000000000000000000000);
      var s17 := Dup2(s16);
      var s18 := MStore(s17);
      var s19 := Pop(s18);
      var s20 := Push1(s19, 0x08);
      var s21 := Add(s20);
      assert s21.Peek(3) == 0x79d;
      assert s21.Peek(6) == 0x342;
      var s22 := Swap2(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Push1(s24, 0x40);
      var s26 := MLoad(s25);
      var s27 := Push1(s26, 0x20);
      var s28 := Dup2(s27);
      var s29 := Dup4(s28);
      var s30 := Sub(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x79d;
      assert s31.Peek(6) == 0x342;
      var s32 := Dup2(s31);
      var s33 := MStore(s32);
      var s34 := Swap1(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MStore(s35);
      var s37 := Dup1(s36);
      var s38 := MLoad(s37);
      var s39 := Swap1(s38);
      var s40 := Push1(s39, 0x20);
      var s41 := Add(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s255(s41, gas - 1)
  }

  /** Node 255
    * Segment Id for this node is: 112
    * Starting at 0x798
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s255(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x798 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x79d

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Keccak256(s0);
      assert s1.Peek(1) == 0x79d;
      assert s1.Peek(4) == 0x342;
      var s2 := Push2(s1, 0x1151);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s256(s3, gas - 1)
  }

  /** Node 256
    * Segment Id for this node is: 182
    * Starting at 0x1151
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s256(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x79d

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x79d;
      assert s1.Peek(4) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x79d;
      assert s11.Peek(6) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x7ae1cfca);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x79d;
      assert s21.Peek(11) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x79d;
      assert s31.Peek(12) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s257(s41, gas - 1)
  }

  /** Node 257
    * Segment Id for this node is: 183
    * Starting at 0x11b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s257(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x79d

    requires s0.stack[11] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x79d;
      assert s1.Peek(12) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s259(s11, gas - 1)
      else
        ExecuteFromCFGNode_s258(s11, gas - 1)
  }

  /** Node 258
    * Segment Id for this node is: 184
    * Starting at 0x11c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s258(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x79d

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x79d;
      assert s1.Peek(15) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 259
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s259(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x79d

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x79d;
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s261(s9, gas - 1)
      else
        ExecuteFromCFGNode_s260(s9, gas - 1)
  }

  /** Node 260
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s260(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x79d

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x79d;
      assert s1.Peek(10) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 261
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s261(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x79d

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x79d;
      assert s1.Peek(9) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x79d;
      assert s11.Peek(8) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s263(s14, gas - 1)
      else
        ExecuteFromCFGNode_s262(s14, gas - 1)
  }

  /** Node 262
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s262(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x79d

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x79d;
      assert s1.Peek(8) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 263
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s263(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x79d

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x79d;
      assert s1.Peek(7) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s264(s8, gas - 1)
  }

  /** Node 264
    * Segment Id for this node is: 113
    * Starting at 0x79d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s264(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x79d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := IsZero(s1);
      var s3 := Push2(s2, 0x0863);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s4, gas - 1)
      else
        ExecuteFromCFGNode_s265(s4, gas - 1)
  }

  /** Node 265
    * Segment Id for this node is: 114
    * Starting at 0x7a3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s265(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7a3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Caller(s0);
      assert s1.Peek(3) == 0x342;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Push2(s3, 0x07f7);
      var s5 := Push1(s4, 0x40);
      var s6 := MLoad(s5);
      var s7 := Dup1(s6);
      var s8 := Push1(s7, 0x40);
      var s9 := Add(s8);
      var s10 := Push1(s9, 0x40);
      var s11 := MStore(s10);
      assert s11.Peek(1) == 0x7f7;
      assert s11.Peek(5) == 0x342;
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
      assert s21.Peek(1) == 0x7f7;
      assert s21.Peek(5) == 0x342;
      var s22 := Push2(s21, 0x11c5);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s266(s23, gas - 1)
  }

  /** Node 266
    * Segment Id for this node is: 185
    * Starting at 0x11c5
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s266(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[1] == 0x7f7

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x7f7;
      assert s1.Peek(5) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push2(s3, 0x1284);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x1284;
      assert s11.Peek(8) == 0x7f7;
      assert s11.Peek(12) == 0x342;
      var s12 := Push32(s11, 0x636f6e74726163742e6164647265737300000000000000000000000000000000);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Pop(s14);
      var s16 := Push1(s15, 0x10);
      var s17 := Add(s16);
      var s18 := Dup3(s17);
      var s19 := Dup1(s18);
      var s20 := MLoad(s19);
      var s21 := Swap1(s20);
      assert s21.Peek(5) == 0x1284;
      assert s21.Peek(9) == 0x7f7;
      assert s21.Peek(13) == 0x342;
      var s22 := Push1(s21, 0x20);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Dup1(s24);
      var s26 := Dup4(s25);
      var s27 := Dup4(s26);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s267(s27, gas - 1)
  }

  /** Node 267
    * Segment Id for this node is: 186
    * Starting at 0x1207
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s267(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x7f7

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0x7f7;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x1244);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s269(s6, gas - 1)
      else
        ExecuteFromCFGNode_s268(s6, gas - 1)
  }

  /** Node 268
    * Segment Id for this node is: 187
    * Starting at 0x1210
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s268(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1210 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x7f7

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0x7f7;
      assert s1.Peek(17) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(9) == 0x1284;
      assert s11.Peek(13) == 0x7f7;
      assert s11.Peek(17) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x1207);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s267(s17, gas - 1)
  }

  /** Node 269
    * Segment Id for this node is: 188
    * Starting at 0x1244
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s269(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1244 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x7f7

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x1284;
      assert s1.Peek(12) == 0x7f7;
      assert s1.Peek(16) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(11) == 0x1284;
      assert s11.Peek(15) == 0x7f7;
      assert s11.Peek(19) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(13) == 0x1284;
      assert s21.Peek(17) == 0x7f7;
      assert s21.Peek(21) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(3) == 0x1284;
      assert s31.Peek(7) == 0x7f7;
      assert s31.Peek(11) == 0x342;
      var s32 := Swap2(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Push1(s34, 0x40);
      var s36 := MLoad(s35);
      var s37 := Push1(s36, 0x20);
      var s38 := Dup2(s37);
      var s39 := Dup4(s38);
      var s40 := Sub(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s270(s41, gas - 1)
  }

  /** Node 270
    * Segment Id for this node is: 189
    * Starting at 0x1273
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s270(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[3] == 0x1284

    requires s0.stack[7] == 0x7f7

    requires s0.stack[11] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0x7f7;
      assert s1.Peek(12) == 0x342;
      var s2 := MStore(s1);
      var s3 := Swap1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := MStore(s4);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Keccak256(s10);
      assert s11.Peek(1) == 0x1284;
      assert s11.Peek(5) == 0x7f7;
      assert s11.Peek(9) == 0x342;
      var s12 := Push2(s11, 0x10ab);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s271(s13, gas - 1)
  }

  /** Node 271
    * Segment Id for this node is: 174
    * Starting at 0x10ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s271(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x1284

    requires s0.stack[5] == 0x7f7

    requires s0.stack[9] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1284;
      assert s1.Peek(5) == 0x7f7;
      assert s1.Peek(9) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x1284;
      assert s11.Peek(7) == 0x7f7;
      assert s11.Peek(11) == 0x342;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x21f8a721);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x1284;
      assert s21.Peek(12) == 0x7f7;
      assert s21.Peek(16) == 0x342;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x1284;
      assert s31.Peek(13) == 0x7f7;
      assert s31.Peek(17) == 0x342;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s272(s41, gas - 1)
  }

  /** Node 272
    * Segment Id for this node is: 175
    * Starting at 0x110e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s272(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[8] == 0x1284

    requires s0.stack[12] == 0x7f7

    requires s0.stack[16] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x1284;
      assert s1.Peek(13) == 0x7f7;
      assert s1.Peek(17) == 0x342;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s274(s11, gas - 1)
      else
        ExecuteFromCFGNode_s273(s11, gas - 1)
  }

  /** Node 273
    * Segment Id for this node is: 176
    * Starting at 0x111b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s273(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0x7f7

    requires s0.stack[19] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x1284;
      assert s1.Peek(16) == 0x7f7;
      assert s1.Peek(20) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 274
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s274(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[11] == 0x1284

    requires s0.stack[15] == 0x7f7

    requires s0.stack[19] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x1284;
      assert s1.Peek(15) == 0x7f7;
      assert s1.Peek(19) == 0x342;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s276(s9, gas - 1)
      else
        ExecuteFromCFGNode_s275(s9, gas - 1)
  }

  /** Node 275
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s275(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0x7f7

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x1284;
      assert s1.Peek(11) == 0x7f7;
      assert s1.Peek(15) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 276
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s276(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[6] == 0x1284

    requires s0.stack[10] == 0x7f7

    requires s0.stack[14] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x1284;
      assert s1.Peek(10) == 0x7f7;
      assert s1.Peek(14) == 0x342;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x1284;
      assert s11.Peek(9) == 0x7f7;
      assert s11.Peek(13) == 0x342;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s278(s14, gas - 1)
      else
        ExecuteFromCFGNode_s277(s14, gas - 1)
  }

  /** Node 277
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s277(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0x7f7

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1284;
      assert s1.Peek(9) == 0x7f7;
      assert s1.Peek(13) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 278
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s278(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[4] == 0x1284

    requires s0.stack[8] == 0x7f7

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1284;
      assert s1.Peek(8) == 0x7f7;
      assert s1.Peek(12) == 0x342;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s279(s8, gas - 1)
  }

  /** Node 279
    * Segment Id for this node is: 190
    * Starting at 0x1284
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s279(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1284 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x7f7

    requires s0.stack[8] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7f7;
      assert s1.Peek(8) == 0x342;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push20(s3, 0xffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Push2(s6, 0x065e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s281(s8, gas - 1)
      else
        ExecuteFromCFGNode_s280(s8, gas - 1)
  }

  /** Node 280
    * Segment Id for this node is: 191
    * Starting at 0x12a2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s280(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x7f7

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(4) == 0x7f7;
      assert s1.Peek(8) == 0x342;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Push32(s3, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s5 := Dup2(s4);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Push1(s7, 0x04);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(5) == 0x7f7;
      assert s11.Peek(9) == 0x342;
      var s12 := Push1(s11, 0x12);
      var s13 := Push1(s12, 0x24);
      var s14 := Dup3(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Push32(s16, 0x436f6e7472616374206e6f7420666f756e640000000000000000000000000000);
      var s18 := Push1(s17, 0x44);
      var s19 := Dup3(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(5) == 0x7f7;
      assert s21.Peek(9) == 0x342;
      var s22 := Swap1(s21);
      var s23 := MLoad(s22);
      var s24 := Swap1(s23);
      var s25 := Dup2(s24);
      var s26 := Swap1(s25);
      var s27 := Sub(s26);
      var s28 := Push1(s27, 0x64);
      var s29 := Add(s28);
      var s30 := Swap1(s29);
      var s31 := Revert(s30);
      // Segment is terminal (Revert, Stop or Return)
      s31
  }

  /** Node 281
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s281(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x7f7

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x7f7;
      assert s1.Peek(7) == 0x342;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s282(s6, gas - 1)
  }

  /** Node 282
    * Segment Id for this node is: 115
    * Starting at 0x7f7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s282(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x342;
      var s2 := Push20(s1, 0xffffffffffffffffffffffffffffffffffffffff);
      var s3 := And(s2);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x0863);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s284(s6, gas - 1)
      else
        ExecuteFromCFGNode_s283(s6, gas - 1)
  }

  /** Node 283
    * Segment Id for this node is: 116
    * Starting at 0x813
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s283(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x813 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Dup1(s7);
      var s9 := Dup1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(5) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Dup2(s12);
      var s14 := Sub(s13);
      var s15 := Dup3(s14);
      var s16 := MStore(s15);
      var s17 := Push1(s16, 0x39);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(5) == 0x342;
      var s22 := Dup1(s21);
      var s23 := Push2(s22, 0x1530);
      var s24 := Push1(s23, 0x39);
      var s25 := Swap2(s24);
      var s26 := CodeCopy(s25);
      var s27 := Push1(s26, 0x40);
      var s28 := Add(s27);
      var s29 := Swap2(s28);
      var s30 := Pop(s29);
      var s31 := Pop(s30);
      assert s31.Peek(3) == 0x342;
      var s32 := Push1(s31, 0x40);
      var s33 := MLoad(s32);
      var s34 := Dup1(s33);
      var s35 := Swap2(s34);
      var s36 := Sub(s35);
      var s37 := Swap1(s36);
      var s38 := Revert(s37);
      // Segment is terminal (Revert, Stop or Return)
      s38
  }

  /** Node 284
    * Segment Id for this node is: 117
    * Starting at 0x863
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 10
    * Net Stack Effect: +10
    * Net Capacity Effect: -10
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s284(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x863 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x342;
      var s2 := Push2(s1, 0x0902);
      var s3 := Push1(s2, 0x01);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Add(s8);
      var s10 := Dup1(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x902;
      assert s11.Peek(8) == 0x342;
      var s12 := Dup2(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Add(s14);
      var s16 := Dup3(s15);
      var s17 := Dup1(s16);
      var s18 := MLoad(s17);
      var s19 := Swap1(s18);
      var s20 := Push1(s19, 0x20);
      var s21 := Add(s20);
      assert s21.Peek(6) == 0x902;
      assert s21.Peek(9) == 0x342;
      var s22 := Swap1(s21);
      var s23 := Dup1(s22);
      var s24 := Dup4(s23);
      var s25 := Dup4(s24);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s285(s25, gas - 1)
  }

  /** Node 285
    * Segment Id for this node is: 118
    * Starting at 0x883
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s285(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x883 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x902;
      assert s1.Peek(12) == 0x342;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x08c0);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s287(s6, gas - 1)
      else
        ExecuteFromCFGNode_s286(s6, gas - 1)
  }

  /** Node 286
    * Segment Id for this node is: 119
    * Starting at 0x88c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s286(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x88c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x902;
      assert s1.Peek(13) == 0x342;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x902;
      assert s11.Peek(13) == 0x342;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0883);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s285(s17, gas - 1)
  }

  /** Node 287
    * Segment Id for this node is: 120
    * Starting at 0x8c0
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s287(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8c0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x902

    requires s0.stack[12] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x902;
      assert s1.Peek(12) == 0x342;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x902;
      assert s11.Peek(15) == 0x342;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x902;
      assert s21.Peek(17) == 0x342;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x902;
      assert s31.Peek(7) == 0x342;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s288(s41, gas - 1)
  }

  /** Node 288
    * Segment Id for this node is: 121
    * Starting at 0x8ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s288(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x902

    requires s0.stack[7] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x902;
      assert s1.Peek(6) == 0x342;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x902;
      assert s11.Peek(5) == 0x342;
      var s12 := Keccak256(s11);
      var s13 := Dup3(s12);
      var s14 := Push2(s13, 0x1308);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s289(s15, gas - 1)
  }

  /** Node 289
    * Segment Id for this node is: 192
    * Starting at 0x1308
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s289(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[2] == 0x902

    requires s0.stack[5] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x902;
      assert s1.Peek(5) == 0x342;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup1(s5);
      var s7 := MLoad(s6);
      var s8 := Push32(s7, 0xabfdcced00000000000000000000000000000000000000000000000000000000);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x04);
      assert s11.Peek(7) == 0x902;
      assert s11.Peek(10) == 0x342;
      var s12 := Dup2(s11);
      var s13 := Add(s12);
      var s14 := Dup7(s13);
      var s15 := Swap1(s14);
      var s16 := MStore(s15);
      var s17 := Dup5(s16);
      var s18 := IsZero(s17);
      var s19 := IsZero(s18);
      var s20 := Push1(s19, 0x24);
      var s21 := Dup3(s20);
      assert s21.Peek(9) == 0x902;
      assert s21.Peek(12) == 0x342;
      var s22 := Add(s21);
      var s23 := MStore(s22);
      var s24 := Swap1(s23);
      var s25 := MLoad(s24);
      var s26 := Push2(s25, 0x0100);
      var s27 := Swap1(s26);
      var s28 := Swap3(s27);
      var s29 := Div(s28);
      var s30 := Push20(s29, 0xffffffffffffffffffffffffffffffffffffffff);
      var s31 := And(s30);
      assert s31.Peek(6) == 0x902;
      assert s31.Peek(9) == 0x342;
      var s32 := Swap3(s31);
      var s33 := Push4(s32, 0xabfdcced);
      var s34 := Swap3(s33);
      var s35 := Push1(s34, 0x44);
      var s36 := Dup1(s35);
      var s37 := Dup5(s36);
      var s38 := Add(s37);
      var s39 := Swap4(s38);
      var s40 := Dup3(s39);
      var s41 := Swap1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s290(s41, gas - 1)
  }

  /** Node 290
    * Segment Id for this node is: 193
    * Starting at 0x1370
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s290(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1370 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[10] == 0x902

    requires s0.stack[13] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(9) == 0x902;
      assert s1.Peek(12) == 0x342;
      var s2 := Add(s1);
      var s3 := Dup2(s2);
      var s4 := Dup4(s3);
      var s5 := Dup8(s4);
      var s6 := Dup1(s5);
      var s7 := ExtCodeSize(s6);
      var s8 := IsZero(s7);
      var s9 := Dup1(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x1382);
      assert s11.Peek(0) == 0x1382;
      assert s11.Peek(14) == 0x902;
      assert s11.Peek(17) == 0x342;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s12, gas - 1)
      else
        ExecuteFromCFGNode_s291(s12, gas - 1)
  }

  /** Node 291
    * Segment Id for this node is: 194
    * Starting at 0x137e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s291(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x137e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[12] == 0x902

    requires s0.stack[15] == 0x342

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(13) == 0x902;
      assert s1.Peek(16) == 0x342;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 292
    * Segment Id for this node is: 47
    * Starting at 0x280
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s292(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x280 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0288);
      var s3 := Push2(s2, 0x0704);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s293(s4, gas - 1)
  }

  /** Node 293
    * Segment Id for this node is: 110
    * Starting at 0x704
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s293(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x704 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0x288

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x288;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05b9);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x5b9;
      assert s11.Peek(4) == 0x288;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push32(s16, 0x6e6f64652e7065722e6d696e69706f6f6c2e7374616b652e6d6178696d756d00);
      var s18 := Dup2(s17);
      var s19 := MStore(s18);
      var s20 := Pop(s19);
      var s21 := Push2(s20, 0x0d14);
      assert s21.Peek(0) == 0xd14;
      assert s21.Peek(2) == 0x5b9;
      assert s21.Peek(4) == 0x288;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s140(s22, gas - 1)
  }

  /** Node 294
    * Segment Id for this node is: 20
    * Starting at 0xc8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s294(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xc8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Dup1(s1);
      var s3 := Push4(s2, 0x01dd1629);
      var s4 := Eq(s3);
      var s5 := Push2(s4, 0x00ef);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s346(s6, gas - 1)
      else
        ExecuteFromCFGNode_s295(s6, gas - 1)
  }

  /** Node 295
    * Segment Id for this node is: 21
    * Starting at 0xd4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s295(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1386a244);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x010b);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s321(s5, gas - 1)
      else
        ExecuteFromCFGNode_s296(s5, gas - 1)
  }

  /** Node 296
    * Segment Id for this node is: 22
    * Starting at 0xdf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s296(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xdf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      var s2 := Push4(s1, 0x1bfcc24e);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x01da);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s297(s5, gas - 1)
      else
        ExecuteFromCFGNode_s10(s5, gas - 1)
  }

  /** Node 297
    * Segment Id for this node is: 37
    * Starting at 0x1da
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s297(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f7);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x01f0);
      assert s11.Peek(0) == 0x1f0;
      assert s11.Peek(4) == 0xf7;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s299(s12, gas - 1)
      else
        ExecuteFromCFGNode_s298(s12, gas - 1)
  }

  /** Node 298
    * Segment Id for this node is: 38
    * Starting at 0x1ec
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s298(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 299
    * Segment Id for this node is: 39
    * Starting at 0x1f0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s299(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0xf7;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 5, 0x0100000000);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0xf7;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x020b);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s301(s15, gas - 1)
      else
        ExecuteFromCFGNode_s300(s15, gas - 1)
  }

  /** Node 300
    * Segment Id for this node is: 40
    * Starting at 0x207
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s300(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x207 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 301
    * Segment Id for this node is: 41
    * Starting at 0x20b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s301(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x20b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf7;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x021d);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s303(s11, gas - 1)
      else
        ExecuteFromCFGNode_s302(s11, gas - 1)
  }

  /** Node 302
    * Segment Id for this node is: 42
    * Starting at 0x219
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s302(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x219 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 303
    * Segment Id for this node is: 43
    * Starting at 0x21d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s303(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0xf7;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 5, 0x0100000000);
      var s16 := Dup4(s15);
      var s17 := Gt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x023f);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s305(s21, gas - 1)
      else
        ExecuteFromCFGNode_s304(s21, gas - 1)
  }

  /** Node 304
    * Segment Id for this node is: 44
    * Starting at 0x23b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s304(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 305
    * Segment Id for this node is: 45
    * Starting at 0x23f
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s305(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0xf7;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup1(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Div(s10);
      assert s11.Peek(8) == 0xf7;
      var s12 := Mul(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0xf7;
      var s22 := Dup1(s21);
      var s23 := Swap4(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0xf7;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      var s34 := Dup1(s33);
      var s35 := Dup3(s34);
      var s36 := Dup5(s35);
      var s37 := CallDataCopy(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s306(s41, gas - 1)
  }

  /** Node 306
    * Segment Id for this node is: 46
    * Starting at 0x26f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s306(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(10) == 0xf7;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x0664);
      var s9 := Swap5(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0x664;
      assert s11.Peek(5) == 0xf7;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s307(s15, gas - 1)
  }

  /** Node 307
    * Segment Id for this node is: 105
    * Starting at 0x664
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s307(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x664 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x065e);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x65e;
      assert s11.Peek(7) == 0xf7;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Dup3(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(7) == 0x65e;
      assert s21.Peek(10) == 0xf7;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup4(s24);
      var s26 := Dup4(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s308(s26, gas - 1)
  }

  /** Node 308
    * Segment Id for this node is: 106
    * Starting at 0x686
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s308(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x686 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0xf7;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x06c3);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s310(s6, gas - 1)
      else
        ExecuteFromCFGNode_s309(s6, gas - 1)
  }

  /** Node 309
    * Segment Id for this node is: 107
    * Starting at 0x68f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s309(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x68f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x65e;
      assert s1.Peek(13) == 0xf7;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x65e;
      assert s11.Peek(13) == 0xf7;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x0686);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s308(s17, gas - 1)
  }

  /** Node 310
    * Segment Id for this node is: 108
    * Starting at 0x6c3
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s310(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0xf7;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x65e;
      assert s11.Peek(15) == 0xf7;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x65e;
      assert s21.Peek(17) == 0xf7;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x65e;
      assert s31.Peek(7) == 0xf7;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s311(s41, gas - 1)
  }

  /** Node 311
    * Segment Id for this node is: 109
    * Starting at 0x6f2
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s311(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x65e;
      assert s1.Peek(6) == 0xf7;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x65e;
      assert s11.Peek(5) == 0xf7;
      var s12 := Keccak256(s11);
      var s13 := Push2(s12, 0x1151);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s312(s14, gas - 1)
  }

  /** Node 312
    * Segment Id for this node is: 182
    * Starting at 0x1151
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s312(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1151 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x65e

    requires s0.stack[4] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x65e;
      assert s1.Peek(4) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x65e;
      assert s11.Peek(6) == 0xf7;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x7ae1cfca);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x65e;
      assert s21.Peek(11) == 0xf7;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x65e;
      assert s31.Peek(12) == 0xf7;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s313(s41, gas - 1)
  }

  /** Node 313
    * Segment Id for this node is: 183
    * Starting at 0x11b4
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s313(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11b4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x65e

    requires s0.stack[11] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0xf7;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s315(s11, gas - 1)
      else
        ExecuteFromCFGNode_s314(s11, gas - 1)
  }

  /** Node 314
    * Segment Id for this node is: 184
    * Starting at 0x11c1
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s314(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x65e;
      assert s1.Peek(15) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 315
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s315(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x65e;
      assert s1.Peek(14) == 0xf7;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s317(s9, gas - 1)
      else
        ExecuteFromCFGNode_s316(s9, gas - 1)
  }

  /** Node 316
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s316(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x65e;
      assert s1.Peek(10) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 317
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s317(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x65e;
      assert s1.Peek(9) == 0xf7;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x65e;
      assert s11.Peek(8) == 0xf7;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s319(s14, gas - 1)
      else
        ExecuteFromCFGNode_s318(s14, gas - 1)
  }

  /** Node 318
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s318(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x65e;
      assert s1.Peek(8) == 0xf7;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 319
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s319(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x65e;
      assert s1.Peek(7) == 0xf7;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s320(s8, gas - 1)
  }

  /** Node 320
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s320(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0xf7;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s6, gas - 1)
  }

  /** Node 321
    * Segment Id for this node is: 26
    * Starting at 0x10b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s321(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x01b1);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Lt(s8);
      var s10 := IsZero(s9);
      var s11 := Push2(s10, 0x0121);
      assert s11.Peek(0) == 0x121;
      assert s11.Peek(4) == 0x1b1;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s323(s12, gas - 1)
      else
        ExecuteFromCFGNode_s322(s12, gas - 1)
  }

  /** Node 322
    * Segment Id for this node is: 27
    * Starting at 0x11d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s322(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 323
    * Segment Id for this node is: 28
    * Starting at 0x121
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s323(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x121 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1b1;
      var s2 := Dup2(s1);
      var s3 := Add(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup2(s5);
      var s7 := Add(s6);
      var s8 := Dup2(s7);
      var s9 := CallDataLoad(s8);
      var s10 := PushN(s9, 5, 0x0100000000);
      var s11 := Dup2(s10);
      assert s11.Peek(6) == 0x1b1;
      var s12 := Gt(s11);
      var s13 := IsZero(s12);
      var s14 := Push2(s13, 0x013c);
      var s15 := JumpI(s14);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s14.stack[1] > 0 then
        ExecuteFromCFGNode_s325(s15, gas - 1)
      else
        ExecuteFromCFGNode_s324(s15, gas - 1)
  }

  /** Node 324
    * Segment Id for this node is: 29
    * Starting at 0x138
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s324(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x138 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 325
    * Segment Id for this node is: 30
    * Starting at 0x13c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s325(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x13c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b1;
      var s2 := Dup3(s1);
      var s3 := Add(s2);
      var s4 := Dup4(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup3(s5);
      var s7 := Add(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x014e);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s327(s11, gas - 1)
      else
        ExecuteFromCFGNode_s326(s11, gas - 1)
  }

  /** Node 326
    * Segment Id for this node is: 31
    * Starting at 0x14a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s326(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 327
    * Segment Id for this node is: 32
    * Starting at 0x14e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s327(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Add(s5);
      var s7 := Swap2(s6);
      var s8 := Dup5(s7);
      var s9 := Push1(s8, 0x01);
      var s10 := Dup4(s9);
      var s11 := Mul(s10);
      assert s11.Peek(7) == 0x1b1;
      var s12 := Dup5(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := PushN(s14, 5, 0x0100000000);
      var s16 := Dup4(s15);
      var s17 := Gt(s16);
      var s18 := Or(s17);
      var s19 := IsZero(s18);
      var s20 := Push2(s19, 0x0170);
      var s21 := JumpI(s20);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s20.stack[1] > 0 then
        ExecuteFromCFGNode_s329(s21, gas - 1)
      else
        ExecuteFromCFGNode_s328(s21, gas - 1)
  }

  /** Node 328
    * Segment Id for this node is: 33
    * Starting at 0x16c
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s328(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 329
    * Segment Id for this node is: 34
    * Starting at 0x170
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s329(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x170 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x1b1;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Dup1(s3);
      var s5 := Dup1(s4);
      var s6 := Push1(s5, 0x1f);
      var s7 := Add(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup1(s8);
      var s10 := Swap2(s9);
      var s11 := Div(s10);
      assert s11.Peek(8) == 0x1b1;
      var s12 := Mul(s11);
      var s13 := Push1(s12, 0x20);
      var s14 := Add(s13);
      var s15 := Push1(s14, 0x40);
      var s16 := MLoad(s15);
      var s17 := Swap1(s16);
      var s18 := Dup2(s17);
      var s19 := Add(s18);
      var s20 := Push1(s19, 0x40);
      var s21 := MStore(s20);
      assert s21.Peek(7) == 0x1b1;
      var s22 := Dup1(s21);
      var s23 := Swap4(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Dup2(s26);
      var s28 := Dup2(s27);
      var s29 := MStore(s28);
      var s30 := Push1(s29, 0x20);
      var s31 := Add(s30);
      assert s31.Peek(8) == 0x1b1;
      var s32 := Dup4(s31);
      var s33 := Dup4(s32);
      var s34 := Dup1(s33);
      var s35 := Dup3(s34);
      var s36 := Dup5(s35);
      var s37 := CallDataCopy(s36);
      var s38 := Push1(s37, 0x00);
      var s39 := Swap3(s38);
      var s40 := Add(s39);
      var s41 := Swap2(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s330(s41, gas - 1)
  }

  /** Node 330
    * Segment Id for this node is: 35
    * Starting at 0x1a0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -9
    * Net Capacity Effect: +9
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s330(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap1(s0);
      assert s1.Peek(10) == 0x1b1;
      var s2 := Swap2(s1);
      var s3 := MStore(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap6(s5);
      var s7 := Pop(s6);
      var s8 := Push2(s7, 0x05be);
      var s9 := Swap5(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0x5be;
      assert s11.Peek(5) == 0x1b1;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s331(s15, gas - 1)
  }

  /** Node 331
    * Segment Id for this node is: 99
    * Starting at 0x5be
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 11
    * Net Stack Effect: +11
    * Net Capacity Effect: -11
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s331(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5be as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1b1;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x065e);
      var s4 := Push1(s3, 0x01);
      var s5 := SLoad(s4);
      var s6 := Dup4(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Add(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(4) == 0x65e;
      assert s11.Peek(7) == 0x1b1;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Dup3(s16);
      var s18 := Dup1(s17);
      var s19 := MLoad(s18);
      var s20 := Swap1(s19);
      var s21 := Push1(s20, 0x20);
      assert s21.Peek(7) == 0x65e;
      assert s21.Peek(10) == 0x1b1;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Dup1(s23);
      var s25 := Dup4(s24);
      var s26 := Dup4(s25);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s332(s26, gas - 1)
  }

  /** Node 332
    * Segment Id for this node is: 100
    * Starting at 0x5e0
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s332(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x1b1;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Lt(s3);
      var s5 := Push2(s4, 0x061d);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s334(s6, gas - 1)
      else
        ExecuteFromCFGNode_s333(s6, gas - 1)
  }

  /** Node 333
    * Segment Id for this node is: 101
    * Starting at 0x5e9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s333(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5e9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup1(s0);
      assert s1.Peek(10) == 0x65e;
      assert s1.Peek(13) == 0x1b1;
      var s2 := MLoad(s1);
      var s3 := Dup3(s2);
      var s4 := MStore(s3);
      var s5 := Push32(s4, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := Add(s7);
      var s9 := Swap2(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Swap2(s10);
      assert s11.Peek(10) == 0x65e;
      assert s11.Peek(13) == 0x1b1;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := Swap2(s13);
      var s15 := Add(s14);
      var s16 := Push2(s15, 0x05e0);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s332(s17, gas - 1)
  }

  /** Node 334
    * Segment Id for this node is: 102
    * Starting at 0x61d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s334(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[9] == 0x65e

    requires s0.stack[12] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x1b1;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup4(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Sub(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Exp(s6);
      var s8 := Sub(s7);
      var s9 := Dup1(s8);
      var s10 := Not(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(12) == 0x65e;
      assert s11.Peek(15) == 0x1b1;
      var s12 := MLoad(s11);
      var s13 := And(s12);
      var s14 := Dup2(s13);
      var s15 := Dup5(s14);
      var s16 := MLoad(s15);
      var s17 := And(s16);
      var s18 := Dup1(s17);
      var s19 := Dup3(s18);
      var s20 := Or(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(14) == 0x65e;
      assert s21.Peek(17) == 0x1b1;
      var s22 := MStore(s21);
      var s23 := Pop(s22);
      var s24 := Pop(s23);
      var s25 := Pop(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Swap1(s28);
      var s30 := Pop(s29);
      var s31 := Add(s30);
      assert s31.Peek(4) == 0x65e;
      assert s31.Peek(7) == 0x1b1;
      var s32 := Swap3(s31);
      var s33 := Pop(s32);
      var s34 := Pop(s33);
      var s35 := Pop(s34);
      var s36 := Push1(s35, 0x40);
      var s37 := MLoad(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Dup2(s38);
      var s40 := Dup4(s39);
      var s41 := Sub(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s335(s41, gas - 1)
  }

  /** Node 335
    * Segment Id for this node is: 103
    * Starting at 0x64c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s335(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x64c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Sub(s0);
      assert s1.Peek(3) == 0x65e;
      assert s1.Peek(6) == 0x1b1;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := MStore(s5);
      var s7 := Dup1(s6);
      var s8 := MLoad(s7);
      var s9 := Swap1(s8);
      var s10 := Push1(s9, 0x20);
      var s11 := Add(s10);
      assert s11.Peek(2) == 0x65e;
      assert s11.Peek(5) == 0x1b1;
      var s12 := Keccak256(s11);
      var s13 := Push2(s12, 0x10ab);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s336(s14, gas - 1)
  }

  /** Node 336
    * Segment Id for this node is: 174
    * Starting at 0x10ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +7
    * Net Capacity Effect: -7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s336(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x10ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x65e

    requires s0.stack[4] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x65e;
      assert s1.Peek(4) == 0x1b1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x01);
      var s5 := Swap1(s4);
      var s6 := SLoad(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0100);
      var s9 := Exp(s8);
      var s10 := Swap1(s9);
      var s11 := Div(s10);
      assert s11.Peek(3) == 0x65e;
      assert s11.Peek(6) == 0x1b1;
      var s12 := Push20(s11, 0xffffffffffffffffffffffffffffffffffffffff);
      var s13 := And(s12);
      var s14 := Push20(s13, 0xffffffffffffffffffffffffffffffffffffffff);
      var s15 := And(s14);
      var s16 := Push4(s15, 0x21f8a721);
      var s17 := Dup4(s16);
      var s18 := Push1(s17, 0x40);
      var s19 := MLoad(s18);
      var s20 := Dup3(s19);
      var s21 := Push4(s20, 0xffffffff);
      assert s21.Peek(8) == 0x65e;
      assert s21.Peek(11) == 0x1b1;
      var s22 := And(s21);
      var s23 := Push1(s22, 0xe0);
      var s24 := Shl(s23);
      var s25 := Dup2(s24);
      var s26 := MStore(s25);
      var s27 := Push1(s26, 0x04);
      var s28 := Add(s27);
      var s29 := Dup1(s28);
      var s30 := Dup3(s29);
      var s31 := Dup2(s30);
      assert s31.Peek(9) == 0x65e;
      assert s31.Peek(12) == 0x1b1;
      var s32 := MStore(s31);
      var s33 := Push1(s32, 0x20);
      var s34 := Add(s33);
      var s35 := Swap2(s34);
      var s36 := Pop(s35);
      var s37 := Pop(s36);
      var s38 := Push1(s37, 0x20);
      var s39 := Push1(s38, 0x40);
      var s40 := MLoad(s39);
      var s41 := Dup1(s40);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s337(s41, gas - 1)
  }

  /** Node 337
    * Segment Id for this node is: 175
    * Starting at 0x110e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s337(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x110e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[8] == 0x65e

    requires s0.stack[11] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup4(s0);
      assert s1.Peek(9) == 0x65e;
      assert s1.Peek(12) == 0x1b1;
      var s2 := Sub(s1);
      var s3 := Dup2(s2);
      var s4 := Dup7(s3);
      var s5 := Dup1(s4);
      var s6 := ExtCodeSize(s5);
      var s7 := IsZero(s6);
      var s8 := Dup1(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x111f);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s339(s11, gas - 1)
      else
        ExecuteFromCFGNode_s338(s11, gas - 1)
  }

  /** Node 338
    * Segment Id for this node is: 176
    * Starting at 0x111b
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s338(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(12) == 0x65e;
      assert s1.Peek(15) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 339
    * Segment Id for this node is: 177
    * Starting at 0x111f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s339(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x111f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[11] == 0x65e

    requires s0.stack[14] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x65e;
      assert s1.Peek(14) == 0x1b1;
      var s2 := Pop(s1);
      var s3 := Gas(s2);
      var s4 := StaticCall(s3);
      var s5 := IsZero(s4);
      var s6 := Dup1(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x1133);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s341(s9, gas - 1)
      else
        ExecuteFromCFGNode_s340(s9, gas - 1)
  }

  /** Node 340
    * Segment Id for this node is: 178
    * Starting at 0x112a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s340(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x112a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(7) == 0x65e;
      assert s1.Peek(10) == 0x1b1;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 341
    * Segment Id for this node is: 179
    * Starting at 0x1133
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s341(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1133 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[6] == 0x65e

    requires s0.stack[9] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x65e;
      assert s1.Peek(9) == 0x1b1;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Push1(s5, 0x40);
      var s7 := MLoad(s6);
      var s8 := ReturnDataSize(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup2(s9);
      var s11 := Lt(s10);
      assert s11.Peek(5) == 0x65e;
      assert s11.Peek(8) == 0x1b1;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x1149);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s343(s14, gas - 1)
      else
        ExecuteFromCFGNode_s342(s14, gas - 1)
  }

  /** Node 342
    * Segment Id for this node is: 180
    * Starting at 0x1145
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s342(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1145 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x65e;
      assert s1.Peek(8) == 0x1b1;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 343
    * Segment Id for this node is: 181
    * Starting at 0x1149
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s343(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1149 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[4] == 0x65e

    requires s0.stack[7] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x65e;
      assert s1.Peek(7) == 0x1b1;
      var s2 := Pop(s1);
      var s3 := MLoad(s2);
      var s4 := Swap3(s3);
      var s5 := Swap2(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s344(s8, gas - 1)
  }

  /** Node 344
    * Segment Id for this node is: 104
    * Starting at 0x65e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s344(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x65e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x1b1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1b1;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s345(s6, gas - 1)
  }

  /** Node 345
    * Segment Id for this node is: 36
    * Starting at 0x1b1
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s345(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x40);
      var s3 := Dup1(s2);
      var s4 := MLoad(s3);
      var s5 := Push20(s4, 0xffffffffffffffffffffffffffffffffffffffff);
      var s6 := Swap1(s5);
      var s7 := Swap3(s6);
      var s8 := And(s7);
      var s9 := Dup3(s8);
      var s10 := MStore(s9);
      var s11 := MLoad(s10);
      var s12 := Swap1(s11);
      var s13 := Dup2(s12);
      var s14 := Swap1(s13);
      var s15 := Sub(s14);
      var s16 := Push1(s15, 0x20);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Return(s18);
      // Segment is terminal (Revert, Stop or Return)
      s19
  }

  /** Node 346
    * Segment Id for this node is: 24
    * Starting at 0xef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s346(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x00f7);
      var s3 := Push2(s2, 0x0596);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s347(s4, gas - 1)
  }

  /** Node 347
    * Segment Id for this node is: 97
    * Starting at 0x596
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s347(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x596 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    requires s0.stack[0] == 0xf7

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0xf7;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x05b9);
      var s4 := Push1(s3, 0x40);
      var s5 := MLoad(s4);
      var s6 := Dup1(s5);
      var s7 := Push1(s6, 0x60);
      var s8 := Add(s7);
      var s9 := Push1(s8, 0x40);
      var s10 := MStore(s9);
      var s11 := Dup1(s10);
      assert s11.Peek(2) == 0x5b9;
      assert s11.Peek(4) == 0xf7;
      var s12 := Push1(s11, 0x28);
      var s13 := Dup2(s12);
      var s14 := MStore(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Add(s15);
      var s17 := Push2(s16, 0x1508);
      var s18 := Push1(s17, 0x28);
      var s19 := Swap2(s18);
      var s20 := CodeCopy(s19);
      var s21 := Push2(s20, 0x0664);
      assert s21.Peek(0) == 0x664;
      assert s21.Peek(2) == 0x5b9;
      assert s21.Peek(4) == 0xf7;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s22, gas - 1)
  }

  /** Node 348
    * Segment Id for this node is: 23
    * Starting at 0xea
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s348(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xea as nat
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
