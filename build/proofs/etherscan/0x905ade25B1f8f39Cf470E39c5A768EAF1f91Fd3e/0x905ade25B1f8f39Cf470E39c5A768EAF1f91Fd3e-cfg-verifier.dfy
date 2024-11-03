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
      var s4 := Push1(s3, 0x04);
      var s5 := CallDataSize(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x0029);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s153(s8, gas - 1)
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
      var s6 := Push4(s5, 0x131e7e1c);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x002e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s149(s9, gas - 1)
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
      var s2 := Push4(s1, 0x259debfe);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x006a);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s5, gas - 1)
      else
        ExecuteFromCFGNode_s3(s5, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 3
    * Starting at 0x29
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
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
      var s1 := JumpDest(s0);
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Revert(s3);
      // Segment is terminal (Revert, Stop or Return)
      s4
  }

  /** Node 4
    * Segment Id for this node is: 8
    * Starting at 0x6a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x6a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x007d);
      var s3 := Push2(s2, 0x0078);
      var s4 := CallDataSize(s3);
      var s5 := Push1(s4, 0x04);
      var s6 := Push2(s5, 0x03ec);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s5(s7, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 59
    * Starting at 0x3ec
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ec as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x78

    requires s0.stack[3] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x78;
      assert s1.Peek(3) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x03ff);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s11, gas - 1)
      else
        ExecuteFromCFGNode_s6(s11, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 60
    * Starting at 0x3fb
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3fb as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x78;
      assert s1.Peek(6) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 7
    * Segment Id for this node is: 61
    * Starting at 0x3ff
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x78

    requires s0.stack[5] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x78;
      assert s1.Peek(5) == 0x7d;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0417);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s9(s10, gas - 1)
      else
        ExecuteFromCFGNode_s8(s10, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 62
    * Starting at 0x413
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x413 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 9
    * Segment Id for this node is: 63
    * Starting at 0x417
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x417 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0x7d;
      var s2 := Swap1(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Push1(s5, 0x60);
      var s7 := Dup3(s6);
      var s8 := Dup8(s7);
      var s9 := Sub(s8);
      var s10 := SLt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(7) == 0x78;
      assert s11.Peek(8) == 0x7d;
      var s12 := Push2(s11, 0x042b);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s11(s13, gas - 1)
      else
        ExecuteFromCFGNode_s10(s13, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 64
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
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 11
    * Segment Id for this node is: 65
    * Starting at 0x42b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x42b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0x7d;
      var s2 := Push2(s1, 0x0433);
      var s3 := Push2(s2, 0x0222);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s12(s4, gas - 1)
  }

  /** Node 12
    * Segment Id for this node is: 27
    * Starting at 0x222
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x222 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x433

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x433;
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x60);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup2(s7);
      var s9 := Gt(s8);
      var s10 := Dup3(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x433;
      assert s11.Peek(12) == 0x78;
      assert s11.Peek(13) == 0x7d;
      var s12 := Lt(s11);
      var s13 := Or(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x021c);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s15(s16, gas - 1)
      else
        ExecuteFromCFGNode_s13(s16, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 28
    * Starting at 0x23e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x23e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x433

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x021c);
      assert s1.Peek(0) == 0x21c;
      assert s1.Peek(3) == 0x433;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s3, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x21c

    requires s0.stack[3] == 0x433

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x21c;
      assert s1.Peek(3) == 0x433;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
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
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(5) == 0x433;
      assert s11.Peek(12) == 0x78;
      assert s11.Peek(13) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 15
    * Segment Id for this node is: 26
    * Starting at 0x21c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[2] == 0x433

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x433;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s5, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 66
    * Starting at 0x433
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x433 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[7] == 0x78

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0x7d;
      var s2 := Dup3(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x043e);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0245);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s17(s7, gas - 1)
  }

  /** Node 17
    * Segment Id for this node is: 29
    * Starting at 0x245
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x43e

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x43e;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x025a);
      assert s11.Peek(0) == 0x25a;
      assert s11.Peek(3) == 0x43e;
      assert s11.Peek(12) == 0x78;
      assert s11.Peek(13) == 0x7d;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s19(s12, gas - 1)
      else
        ExecuteFromCFGNode_s18(s12, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 30
    * Starting at 0x256
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x43e

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x43e;
      assert s1.Peek(11) == 0x78;
      assert s1.Peek(12) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 19
    * Segment Id for this node is: 31
    * Starting at 0x25a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[1] == 0x43e

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x43e;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s20(s3, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 67
    * Starting at 0x43e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Dup3(s7);
      var s9 := Dup2(s8);
      var s10 := Gt(s9);
      var s11 := IsZero(s10);
      assert s11.Peek(9) == 0x78;
      assert s11.Peek(10) == 0x7d;
      var s12 := Push2(s11, 0x0452);
      var s13 := JumpI(s12);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s12.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s13, gas - 1)
      else
        ExecuteFromCFGNode_s21(s13, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 68
    * Starting at 0x44e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 22
    * Segment Id for this node is: 69
    * Starting at 0x452
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x452 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0x7d;
      var s2 := Push2(s1, 0x045e);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x026d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s8, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 34
    * Starting at 0x26d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[2] == 0x45e

    requires s0.stack[11] == 0x78

    requires s0.stack[12] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x45e;
      assert s1.Peek(11) == 0x78;
      assert s1.Peek(12) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x027e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s9, gas - 1)
      else
        ExecuteFromCFGNode_s24(s9, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 35
    * Starting at 0x27a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x45e

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x45e;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 36
    * Starting at 0x27e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[3] == 0x45e

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x45e;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0299);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s28(s10, gas - 1)
      else
        ExecuteFromCFGNode_s26(s10, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 37
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x45e

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0299);
      assert s1.Peek(0) == 0x299;
      assert s1.Peek(6) == 0x45e;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s27(s3, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[0] == 0x299

    requires s0.stack[6] == 0x45e

    requires s0.stack[15] == 0x78

    requires s0.stack[16] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x299;
      assert s1.Peek(6) == 0x45e;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0x7d;
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
      assert s11.Peek(2) == 0x299;
      assert s11.Peek(8) == 0x45e;
      assert s11.Peek(17) == 0x78;
      assert s11.Peek(18) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 28
    * Segment Id for this node is: 38
    * Starting at 0x299
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[5] == 0x45e

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x45e;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x45e;
      assert s11.Peek(17) == 0x78;
      assert s11.Peek(18) == 0x7d;
      var s12 := Push1(s11, 0x3f);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Dup3(s17);
      var s19 := Dup3(s18);
      var s20 := Gt(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(9) == 0x45e;
      assert s21.Peek(18) == 0x78;
      assert s21.Peek(19) == 0x7d;
      var s22 := Dup4(s21);
      var s23 := Lt(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x02c1);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s31(s27, gas - 1)
      else
        ExecuteFromCFGNode_s29(s27, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 39
    * Starting at 0x2ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x45e

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02c1);
      assert s1.Peek(0) == 0x2c1;
      assert s1.Peek(8) == 0x45e;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s3, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[0] == 0x2c1

    requires s0.stack[8] == 0x45e

    requires s0.stack[17] == 0x78

    requires s0.stack[18] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2c1;
      assert s1.Peek(8) == 0x45e;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
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
      assert s11.Peek(2) == 0x2c1;
      assert s11.Peek(10) == 0x45e;
      assert s11.Peek(19) == 0x78;
      assert s11.Peek(20) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 31
    * Segment Id for this node is: 40
    * Starting at 0x2c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x45e

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x45e;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
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
      assert s11.Peek(11) == 0x45e;
      assert s11.Peek(20) == 0x78;
      assert s11.Peek(21) == 0x7d;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x02da);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s33(s17, gas - 1)
      else
        ExecuteFromCFGNode_s32(s17, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 41
    * Starting at 0x2d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x45e

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x45e;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 33
    * Segment Id for this node is: 42
    * Starting at 0x2da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[7] == 0x45e

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x45e;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
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
      assert s11.Peek(9) == 0x45e;
      assert s11.Peek(18) == 0x78;
      assert s11.Peek(19) == 0x7d;
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
      assert s21.Peek(5) == 0x45e;
      assert s21.Peek(14) == 0x78;
      assert s21.Peek(15) == 0x7d;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s34(s28, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 70
    * Starting at 0x45e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0x7d;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := Dup4(s7);
      var s9 := Add(s8);
      var s10 := CallDataLoad(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(9) == 0x78;
      assert s11.Peek(10) == 0x7d;
      var s12 := Dup3(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Dup1(s14);
      var s16 := Swap5(s15);
      var s17 := Pop(s16);
      var s18 := Pop(s17);
      var s19 := Push1(s18, 0x20);
      var s20 := Dup6(s19);
      var s21 := Add(s20);
      assert s21.Peek(7) == 0x78;
      assert s21.Peek(8) == 0x7d;
      var s22 := CallDataLoad(s21);
      var s23 := Swap2(s22);
      var s24 := Pop(s23);
      var s25 := Dup1(s24);
      var s26 := Dup3(s25);
      var s27 := Gt(s26);
      var s28 := IsZero(s27);
      var s29 := Push2(s28, 0x0486);
      var s30 := JumpI(s29);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s29.stack[1] > 0 then
        ExecuteFromCFGNode_s36(s30, gas - 1)
      else
        ExecuteFromCFGNode_s35(s30, gas - 1)
  }

  /** Node 35
    * Segment Id for this node is: 71
    * Starting at 0x482
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x482 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x78;
      assert s1.Peek(8) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 36
    * Segment Id for this node is: 72
    * Starting at 0x486
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x486 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Push2(s2, 0x0493);
      var s4 := Dup6(s3);
      var s5 := Dup3(s4);
      var s6 := Dup7(s5);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x030b);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s9, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 45
    * Starting at 0x30b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x30b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x493

    requires s0.stack[8] == 0x78

    requires s0.stack[9] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x493;
      assert s1.Peek(8) == 0x78;
      assert s1.Peek(9) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0140);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x031e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s39(s10, gas - 1)
      else
        ExecuteFromCFGNode_s38(s10, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 46
    * Starting at 0x31a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x493

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x493;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 39
    * Segment Id for this node is: 47
    * Starting at 0x31e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x31e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x493

    requires s0.stack[9] == 0x78

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x493;
      assert s1.Peek(9) == 0x78;
      assert s1.Peek(10) == 0x7d;
      var s2 := Push2(s1, 0x0326);
      var s3 := Push2(s2, 0x01f8);
      var s4 := Jump(s3);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s4, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 24
    * Starting at 0x1f8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x326

    requires s0.stack[4] == 0x493

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x326;
      assert s1.Peek(4) == 0x493;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0140);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := Push8(s6, 0xffffffffffffffff);
      var s8 := Dup2(s7);
      var s9 := Gt(s8);
      var s10 := Dup3(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(5) == 0x326;
      assert s11.Peek(9) == 0x493;
      assert s11.Peek(15) == 0x78;
      assert s11.Peek(16) == 0x7d;
      var s12 := Lt(s11);
      var s13 := Or(s12);
      var s14 := IsZero(s13);
      var s15 := Push2(s14, 0x021c);
      var s16 := JumpI(s15);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s15.stack[1] > 0 then
        ExecuteFromCFGNode_s43(s16, gas - 1)
      else
        ExecuteFromCFGNode_s41(s16, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 25
    * Starting at 0x215
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x215 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x326

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x021c);
      assert s1.Peek(0) == 0x21c;
      assert s1.Peek(3) == 0x326;
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s42(s3, gas - 1)
  }

  /** Node 42
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[0] == 0x21c

    requires s0.stack[3] == 0x326

    requires s0.stack[7] == 0x493

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x21c;
      assert s1.Peek(3) == 0x326;
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
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
      assert s11.Peek(2) == 0x21c;
      assert s11.Peek(5) == 0x326;
      assert s11.Peek(9) == 0x493;
      assert s11.Peek(15) == 0x78;
      assert s11.Peek(16) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 43
    * Segment Id for this node is: 26
    * Starting at 0x21c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x326

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x326;
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MStore(s2);
      var s4 := Swap1(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s44(s5, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 48
    * Starting at 0x326
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x326 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x493

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x493;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push2(s3, 0x0331);
      var s5 := Dup3(s4);
      var s6 := Push2(s5, 0x025d);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s45(s7, gas - 1)
  }

  /** Node 45
    * Segment Id for this node is: 32
    * Starting at 0x25d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[1] == 0x331

    requires s0.stack[5] == 0x493

    requires s0.stack[11] == 0x78

    requires s0.stack[12] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x331;
      assert s1.Peek(5) == 0x493;
      assert s1.Peek(11) == 0x78;
      assert s1.Peek(12) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0268);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0245);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s7, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 29
    * Starting at 0x245
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x268;
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x493;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x025a);
      assert s11.Peek(0) == 0x25a;
      assert s11.Peek(3) == 0x268;
      assert s11.Peek(6) == 0x331;
      assert s11.Peek(10) == 0x493;
      assert s11.Peek(16) == 0x78;
      assert s11.Peek(17) == 0x7d;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s48(s12, gas - 1)
      else
        ExecuteFromCFGNode_s47(s12, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 30
    * Starting at 0x256
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x268;
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(9) == 0x493;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 48
    * Segment Id for this node is: 31
    * Starting at 0x25a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x331

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x268;
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(8) == 0x493;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 33
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[2] == 0x331

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x331;
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s50(s5, gas - 1)
  }

  /** Node 50
    * Segment Id for this node is: 49
    * Starting at 0x331
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[4] == 0x493

    requires s0.stack[10] == 0x78

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x493;
      assert s1.Peek(10) == 0x78;
      assert s1.Peek(11) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup3(s4);
      var s6 := Add(s5);
      var s7 := CallDataLoad(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(3) == 0x493;
      assert s11.Peek(9) == 0x78;
      assert s11.Peek(10) == 0x7d;
      var s12 := Push1(s11, 0x40);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := CallDataLoad(s14);
      var s16 := Push8(s15, 0xffffffffffffffff);
      var s17 := Dup1(s16);
      var s18 := Dup3(s17);
      var s19 := Gt(s18);
      var s20 := IsZero(s19);
      var s21 := Push2(s20, 0x0358);
      assert s21.Peek(0) == 0x358;
      assert s21.Peek(7) == 0x493;
      assert s21.Peek(13) == 0x78;
      assert s21.Peek(14) == 0x7d;
      var s22 := JumpI(s21);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s21.stack[1] > 0 then
        ExecuteFromCFGNode_s52(s22, gas - 1)
      else
        ExecuteFromCFGNode_s51(s22, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 50
    * Starting at 0x354
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x354 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x493

    requires s0.stack[11] == 0x78

    requires s0.stack[12] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 52
    * Segment Id for this node is: 51
    * Starting at 0x358
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x358 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x493

    requires s0.stack[11] == 0x78

    requires s0.stack[12] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x493;
      assert s1.Peek(11) == 0x78;
      assert s1.Peek(12) == 0x7d;
      var s2 := Push2(s1, 0x0364);
      var s3 := Dup6(s2);
      var s4 := Dup4(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x026d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s53(s8, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 34
    * Starting at 0x26d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x364

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x364;
      assert s1.Peek(8) == 0x493;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x027e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s9, gas - 1)
      else
        ExecuteFromCFGNode_s54(s9, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 35
    * Starting at 0x27a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x364

    requires s0.stack[9] == 0x493

    requires s0.stack[15] == 0x78

    requires s0.stack[16] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x364;
      assert s1.Peek(10) == 0x493;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 55
    * Segment Id for this node is: 36
    * Starting at 0x27e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[3] == 0x364

    requires s0.stack[9] == 0x493

    requires s0.stack[15] == 0x78

    requires s0.stack[16] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x364;
      assert s1.Peek(9) == 0x493;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0299);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s10, gas - 1)
      else
        ExecuteFromCFGNode_s56(s10, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 37
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x364

    requires s0.stack[11] == 0x493

    requires s0.stack[17] == 0x78

    requires s0.stack[18] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0299);
      assert s1.Peek(0) == 0x299;
      assert s1.Peek(6) == 0x364;
      assert s1.Peek(12) == 0x493;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s57(s3, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[0] == 0x299

    requires s0.stack[6] == 0x364

    requires s0.stack[12] == 0x493

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x299;
      assert s1.Peek(6) == 0x364;
      assert s1.Peek(12) == 0x493;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0x7d;
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
      assert s11.Peek(2) == 0x299;
      assert s11.Peek(8) == 0x364;
      assert s11.Peek(14) == 0x493;
      assert s11.Peek(20) == 0x78;
      assert s11.Peek(21) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 58
    * Segment Id for this node is: 38
    * Starting at 0x299
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[5] == 0x364

    requires s0.stack[11] == 0x493

    requires s0.stack[17] == 0x78

    requires s0.stack[18] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x364;
      assert s1.Peek(11) == 0x493;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x364;
      assert s11.Peek(14) == 0x493;
      assert s11.Peek(20) == 0x78;
      assert s11.Peek(21) == 0x7d;
      var s12 := Push1(s11, 0x3f);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Dup3(s17);
      var s19 := Dup3(s18);
      var s20 := Gt(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(9) == 0x364;
      assert s21.Peek(15) == 0x493;
      assert s21.Peek(21) == 0x78;
      assert s21.Peek(22) == 0x7d;
      var s22 := Dup4(s21);
      var s23 := Lt(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x02c1);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s61(s27, gas - 1)
      else
        ExecuteFromCFGNode_s59(s27, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 39
    * Starting at 0x2ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x364

    requires s0.stack[13] == 0x493

    requires s0.stack[19] == 0x78

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02c1);
      assert s1.Peek(0) == 0x2c1;
      assert s1.Peek(8) == 0x364;
      assert s1.Peek(14) == 0x493;
      assert s1.Peek(20) == 0x78;
      assert s1.Peek(21) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s60(s3, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x2c1

    requires s0.stack[8] == 0x364

    requires s0.stack[14] == 0x493

    requires s0.stack[20] == 0x78

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2c1;
      assert s1.Peek(8) == 0x364;
      assert s1.Peek(14) == 0x493;
      assert s1.Peek(20) == 0x78;
      assert s1.Peek(21) == 0x7d;
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
      assert s11.Peek(2) == 0x2c1;
      assert s11.Peek(10) == 0x364;
      assert s11.Peek(16) == 0x493;
      assert s11.Peek(22) == 0x78;
      assert s11.Peek(23) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 61
    * Segment Id for this node is: 40
    * Starting at 0x2c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x364

    requires s0.stack[13] == 0x493

    requires s0.stack[19] == 0x78

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x364;
      assert s1.Peek(13) == 0x493;
      assert s1.Peek(19) == 0x78;
      assert s1.Peek(20) == 0x7d;
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
      assert s11.Peek(11) == 0x364;
      assert s11.Peek(17) == 0x493;
      assert s11.Peek(23) == 0x78;
      assert s11.Peek(24) == 0x7d;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x02da);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s63(s17, gas - 1)
      else
        ExecuteFromCFGNode_s62(s17, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 41
    * Starting at 0x2d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x364

    requires s0.stack[13] == 0x493

    requires s0.stack[19] == 0x78

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x364;
      assert s1.Peek(14) == 0x493;
      assert s1.Peek(20) == 0x78;
      assert s1.Peek(21) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 63
    * Segment Id for this node is: 42
    * Starting at 0x2da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[7] == 0x364

    requires s0.stack[13] == 0x493

    requires s0.stack[19] == 0x78

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x364;
      assert s1.Peek(13) == 0x493;
      assert s1.Peek(19) == 0x78;
      assert s1.Peek(20) == 0x7d;
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
      assert s11.Peek(9) == 0x364;
      assert s11.Peek(15) == 0x493;
      assert s11.Peek(21) == 0x78;
      assert s11.Peek(22) == 0x7d;
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
      assert s21.Peek(5) == 0x364;
      assert s21.Peek(11) == 0x493;
      assert s21.Peek(17) == 0x78;
      assert s21.Peek(18) == 0x7d;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s28, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 52
    * Starting at 0x364
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x364 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0375);
      var s7 := Push1(s6, 0x60);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x02fa);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s65(s11, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 43
    * Starting at 0x2fa
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fa as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x375

    requires s0.stack[7] == 0x493

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x375;
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push1(s3, 0xff);
      var s5 := Dup2(s4);
      var s6 := And(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0268);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s67(s10, gas - 1)
      else
        ExecuteFromCFGNode_s66(s10, gas - 1)
  }

  /** Node 66
    * Segment Id for this node is: 44
    * Starting at 0x307
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x307 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x375

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(3) == 0x375;
      assert s1.Peek(9) == 0x493;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 67
    * Segment Id for this node is: 33
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x375

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x375;
      assert s1.Peek(8) == 0x493;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s5, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 53
    * Starting at 0x375
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x375 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Push1(s1, 0x60);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x80);
      var s7 := Dup5(s6);
      var s8 := Add(s7);
      var s9 := CallDataLoad(s8);
      var s10 := Push1(s9, 0x80);
      var s11 := Dup5(s10);
      assert s11.Peek(8) == 0x493;
      assert s11.Peek(14) == 0x78;
      assert s11.Peek(15) == 0x7d;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0xa0);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := CallDataLoad(s16);
      var s18 := Push1(s17, 0xa0);
      var s19 := Dup5(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(5) == 0x493;
      assert s21.Peek(11) == 0x78;
      assert s21.Peek(12) == 0x7d;
      var s22 := Push1(s21, 0xc0);
      var s23 := Dup5(s22);
      var s24 := Add(s23);
      var s25 := CallDataLoad(s24);
      var s26 := Push1(s25, 0xc0);
      var s27 := Dup5(s26);
      var s28 := Add(s27);
      var s29 := MStore(s28);
      var s30 := Push2(s29, 0x03a4);
      var s31 := Push1(s30, 0xe0);
      assert s31.Peek(1) == 0x3a4;
      assert s31.Peek(7) == 0x493;
      assert s31.Peek(13) == 0x78;
      assert s31.Peek(14) == 0x7d;
      var s32 := Dup6(s31);
      var s33 := Add(s32);
      var s34 := Push2(s33, 0x025d);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s69(s35, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 32
    * Starting at 0x25d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x3a4

    requires s0.stack[7] == 0x493

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3a4;
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0268);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0245);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s7, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 29
    * Starting at 0x245
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x3a4

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x268;
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(10) == 0x493;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x025a);
      assert s11.Peek(0) == 0x25a;
      assert s11.Peek(3) == 0x268;
      assert s11.Peek(6) == 0x3a4;
      assert s11.Peek(12) == 0x493;
      assert s11.Peek(18) == 0x78;
      assert s11.Peek(19) == 0x7d;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s72(s12, gas - 1)
      else
        ExecuteFromCFGNode_s71(s12, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 30
    * Starting at 0x256
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x3a4

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x268;
      assert s1.Peek(5) == 0x3a4;
      assert s1.Peek(11) == 0x493;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 72
    * Segment Id for this node is: 31
    * Starting at 0x25a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x3a4

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x268;
      assert s1.Peek(4) == 0x3a4;
      assert s1.Peek(10) == 0x493;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 33
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x3a4

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3a4;
      assert s1.Peek(8) == 0x493;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s74(s5, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 54
    * Starting at 0x3a4
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a4 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Push1(s1, 0xe0);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0100);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Push2(s8, 0x03b9);
      var s10 := Dup3(s9);
      var s11 := Dup6(s10);
      assert s11.Peek(2) == 0x3b9;
      assert s11.Peek(8) == 0x493;
      assert s11.Peek(14) == 0x78;
      assert s11.Peek(15) == 0x7d;
      var s12 := Add(s11);
      var s13 := Push2(s12, 0x025d);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s14, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 32
    * Starting at 0x25d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[1] == 0x3b9

    requires s0.stack[7] == 0x493

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3b9;
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0268);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0245);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s7, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 29
    * Starting at 0x245
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x3b9

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x268;
      assert s1.Peek(4) == 0x3b9;
      assert s1.Peek(10) == 0x493;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x025a);
      assert s11.Peek(0) == 0x25a;
      assert s11.Peek(3) == 0x268;
      assert s11.Peek(6) == 0x3b9;
      assert s11.Peek(12) == 0x493;
      assert s11.Peek(18) == 0x78;
      assert s11.Peek(19) == 0x7d;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s78(s12, gas - 1)
      else
        ExecuteFromCFGNode_s77(s12, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 30
    * Starting at 0x256
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x3b9

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x268;
      assert s1.Peek(5) == 0x3b9;
      assert s1.Peek(11) == 0x493;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 78
    * Segment Id for this node is: 31
    * Starting at 0x25a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[1] == 0x268

    requires s0.stack[4] == 0x3b9

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x268;
      assert s1.Peek(4) == 0x3b9;
      assert s1.Peek(10) == 0x493;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s3, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 33
    * Starting at 0x268
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x268 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[2] == 0x3b9

    requires s0.stack[8] == 0x493

    requires s0.stack[14] == 0x78

    requires s0.stack[15] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3b9;
      assert s1.Peek(8) == 0x493;
      assert s1.Peek(14) == 0x78;
      assert s1.Peek(15) == 0x7d;
      var s2 := Swap2(s1);
      var s3 := Swap1(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s5, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 55
    * Starting at 0x3b9
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3b9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Dup3(s1);
      var s3 := Dup5(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Push2(s5, 0x0120);
      var s7 := Swap2(s6);
      var s8 := Pop(s7);
      var s9 := Dup2(s8);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(6) == 0x493;
      assert s11.Peek(12) == 0x78;
      assert s11.Peek(13) == 0x7d;
      var s12 := CallDataLoad(s11);
      var s13 := Dup2(s12);
      var s14 := Dup2(s13);
      var s15 := Gt(s14);
      var s16 := IsZero(s15);
      var s17 := Push2(s16, 0x03d3);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s82(s18, gas - 1)
      else
        ExecuteFromCFGNode_s81(s18, gas - 1)
  }

  /** Node 81
    * Segment Id for this node is: 56
    * Starting at 0x3cf
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 82
    * Segment Id for this node is: 57
    * Starting at 0x3d3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3d3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 15

    requires s0.stack[6] == 0x493

    requires s0.stack[12] == 0x78

    requires s0.stack[13] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x493;
      assert s1.Peek(12) == 0x78;
      assert s1.Peek(13) == 0x7d;
      var s2 := Push2(s1, 0x03df);
      var s3 := Dup7(s2);
      var s4 := Dup3(s3);
      var s5 := Dup8(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x026d);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s83(s8, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 34
    * Starting at 0x26d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x26d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 18

    requires s0.stack[2] == 0x3df

    requires s0.stack[9] == 0x493

    requires s0.stack[15] == 0x78

    requires s0.stack[16] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x3df;
      assert s1.Peek(9) == 0x493;
      assert s1.Peek(15) == 0x78;
      assert s1.Peek(16) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x027e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s9, gas - 1)
      else
        ExecuteFromCFGNode_s84(s9, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 35
    * Starting at 0x27a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x3df

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x3df;
      assert s1.Peek(11) == 0x493;
      assert s1.Peek(17) == 0x78;
      assert s1.Peek(18) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 85
    * Segment Id for this node is: 36
    * Starting at 0x27e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x27e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[3] == 0x3df

    requires s0.stack[10] == 0x493

    requires s0.stack[16] == 0x78

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3df;
      assert s1.Peek(10) == 0x493;
      assert s1.Peek(16) == 0x78;
      assert s1.Peek(17) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push8(s3, 0xffffffffffffffff);
      var s5 := Dup1(s4);
      var s6 := Dup3(s5);
      var s7 := Gt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0299);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s88(s10, gas - 1)
      else
        ExecuteFromCFGNode_s86(s10, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 37
    * Starting at 0x292
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x292 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x3df

    requires s0.stack[12] == 0x493

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0299);
      assert s1.Peek(0) == 0x299;
      assert s1.Peek(6) == 0x3df;
      assert s1.Peek(13) == 0x493;
      assert s1.Peek(19) == 0x78;
      assert s1.Peek(20) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s87(s3, gas - 1)
  }

  /** Node 87
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[0] == 0x299

    requires s0.stack[6] == 0x3df

    requires s0.stack[13] == 0x493

    requires s0.stack[19] == 0x78

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x299;
      assert s1.Peek(6) == 0x3df;
      assert s1.Peek(13) == 0x493;
      assert s1.Peek(19) == 0x78;
      assert s1.Peek(20) == 0x7d;
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
      assert s11.Peek(2) == 0x299;
      assert s11.Peek(8) == 0x3df;
      assert s11.Peek(15) == 0x493;
      assert s11.Peek(21) == 0x78;
      assert s11.Peek(22) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 88
    * Segment Id for this node is: 38
    * Starting at 0x299
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x299 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[5] == 0x3df

    requires s0.stack[12] == 0x493

    requires s0.stack[18] == 0x78

    requires s0.stack[19] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x3df;
      assert s1.Peek(12) == 0x493;
      assert s1.Peek(18) == 0x78;
      assert s1.Peek(19) == 0x7d;
      var s2 := Push1(s1, 0x40);
      var s3 := MLoad(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := Push1(s6, 0x1f);
      var s8 := Not(s7);
      var s9 := Swap1(s8);
      var s10 := Dup2(s9);
      var s11 := And(s10);
      assert s11.Peek(8) == 0x3df;
      assert s11.Peek(15) == 0x493;
      assert s11.Peek(21) == 0x78;
      assert s11.Peek(22) == 0x7d;
      var s12 := Push1(s11, 0x3f);
      var s13 := Add(s12);
      var s14 := And(s13);
      var s15 := Dup2(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Dup3(s17);
      var s19 := Dup3(s18);
      var s20 := Gt(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(9) == 0x3df;
      assert s21.Peek(16) == 0x493;
      assert s21.Peek(22) == 0x78;
      assert s21.Peek(23) == 0x7d;
      var s22 := Dup4(s21);
      var s23 := Lt(s22);
      var s24 := Or(s23);
      var s25 := IsZero(s24);
      var s26 := Push2(s25, 0x02c1);
      var s27 := JumpI(s26);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s26.stack[1] > 0 then
        ExecuteFromCFGNode_s91(s27, gas - 1)
      else
        ExecuteFromCFGNode_s89(s27, gas - 1)
  }

  /** Node 89
    * Segment Id for this node is: 39
    * Starting at 0x2ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x3df

    requires s0.stack[14] == 0x493

    requires s0.stack[20] == 0x78

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x02c1);
      assert s1.Peek(0) == 0x2c1;
      assert s1.Peek(8) == 0x3df;
      assert s1.Peek(15) == 0x493;
      assert s1.Peek(21) == 0x78;
      assert s1.Peek(22) == 0x7d;
      var s2 := Push2(s1, 0x01e2);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s3, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 23
    * Starting at 0x1e2
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 24

    requires s0.stack[0] == 0x2c1

    requires s0.stack[8] == 0x3df

    requires s0.stack[15] == 0x493

    requires s0.stack[21] == 0x78

    requires s0.stack[22] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x2c1;
      assert s1.Peek(8) == 0x3df;
      assert s1.Peek(15) == 0x493;
      assert s1.Peek(21) == 0x78;
      assert s1.Peek(22) == 0x7d;
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
      assert s11.Peek(2) == 0x2c1;
      assert s11.Peek(10) == 0x3df;
      assert s11.Peek(17) == 0x493;
      assert s11.Peek(23) == 0x78;
      assert s11.Peek(24) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 91
    * Segment Id for this node is: 40
    * Starting at 0x2c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x3df

    requires s0.stack[14] == 0x493

    requires s0.stack[20] == 0x78

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3df;
      assert s1.Peek(14) == 0x493;
      assert s1.Peek(20) == 0x78;
      assert s1.Peek(21) == 0x7d;
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
      assert s11.Peek(11) == 0x3df;
      assert s11.Peek(18) == 0x493;
      assert s11.Peek(24) == 0x78;
      assert s11.Peek(25) == 0x7d;
      var s12 := Add(s11);
      var s13 := Add(s12);
      var s14 := Gt(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x02da);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s93(s17, gas - 1)
      else
        ExecuteFromCFGNode_s92(s17, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 41
    * Starting at 0x2d6
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2d6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x3df

    requires s0.stack[14] == 0x493

    requires s0.stack[20] == 0x78

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(8) == 0x3df;
      assert s1.Peek(15) == 0x493;
      assert s1.Peek(21) == 0x78;
      assert s1.Peek(22) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 93
    * Segment Id for this node is: 42
    * Starting at 0x2da
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2da as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[7] == 0x3df

    requires s0.stack[14] == 0x493

    requires s0.stack[20] == 0x78

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x3df;
      assert s1.Peek(14) == 0x493;
      assert s1.Peek(20) == 0x78;
      assert s1.Peek(21) == 0x7d;
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
      assert s11.Peek(9) == 0x3df;
      assert s11.Peek(16) == 0x493;
      assert s11.Peek(22) == 0x78;
      assert s11.Peek(23) == 0x7d;
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
      assert s21.Peek(5) == 0x3df;
      assert s21.Peek(12) == 0x493;
      assert s21.Peek(18) == 0x78;
      assert s21.Peek(19) == 0x7d;
      var s22 := Pop(s21);
      var s23 := Pop(s22);
      var s24 := Swap3(s23);
      var s25 := Swap2(s24);
      var s26 := Pop(s25);
      var s27 := Pop(s26);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s28, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 58
    * Starting at 0x3df
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3df as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[7] == 0x493

    requires s0.stack[13] == 0x78

    requires s0.stack[14] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x493;
      assert s1.Peek(13) == 0x78;
      assert s1.Peek(14) == 0x7d;
      var s2 := Dup4(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := MStore(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Swap3(s8);
      var s10 := Swap2(s9);
      var s11 := Pop(s10);
      assert s11.Peek(1) == 0x493;
      assert s11.Peek(8) == 0x78;
      assert s11.Peek(9) == 0x7d;
      var s12 := Pop(s11);
      var s13 := Jump(s12);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s95(s13, gas - 1)
  }

  /** Node 95
    * Segment Id for this node is: 73
    * Starting at 0x493
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x493 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x78

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x78;
      assert s1.Peek(7) == 0x7d;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Pop(s5);
      var s7 := Swap3(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s10, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 9
    * Starting at 0x78
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x78 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7d;
      var s2 := Push2(s1, 0x007f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s97(s3, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 11
    * Starting at 0x7f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := SLoad(s3);
      var s5 := Dup4(s4);
      var s6 := MLoad(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup6(s7);
      var s9 := Add(s8);
      var s10 := MLoad(s9);
      var s11 := Push1(s10, 0x40);
      assert s11.Peek(7) == 0x7d;
      var s12 := Dup1(s11);
      var s13 := Dup8(s12);
      var s14 := Add(s13);
      var s15 := MLoad(s14);
      var s16 := Swap1(s15);
      var s17 := MLoad(s16);
      var s18 := Push32(s17, 0x1688f0b900000000000000000000000000000000000000000000000000000000);
      var s19 := Dup2(s18);
      var s20 := MStore(s19);
      var s21 := Push1(s20, 0x01);
      assert s21.Peek(9) == 0x7d;
      var s22 := Push1(s21, 0x01);
      var s23 := Push1(s22, 0xa0);
      var s24 := Shl(s23);
      var s25 := Sub(s24);
      var s26 := Swap1(s25);
      var s27 := Swap5(s26);
      var s28 := And(s27);
      var s29 := Swap4(s28);
      var s30 := Push4(s29, 0x1688f0b9);
      var s31 := Swap4(s30);
      assert s31.Peek(9) == 0x7d;
      var s32 := Push2(s31, 0x00d7);
      var s33 := Swap4(s32);
      var s34 := Swap1(s33);
      var s35 := Swap3(s34);
      var s36 := Swap1(s35);
      var s37 := Swap2(s36);
      var s38 := Push1(s37, 0x04);
      var s39 := Add(s38);
      var s40 := Push2(s39, 0x04ea);
      var s41 := Jump(s40);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s41, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 80
    * Starting at 0x4ea
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4ea as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[4] == 0xd7

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0xd7;
      assert s1.Peek(10) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup5(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := MStore(s9);
      var s11 := Push1(s10, 0x60);
      assert s11.Peek(5) == 0xd7;
      assert s11.Peek(11) == 0x7d;
      var s12 := Push1(s11, 0x20);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := MStore(s14);
      var s16 := Push1(s15, 0x00);
      var s17 := Push2(s16, 0x050c);
      var s18 := Push1(s17, 0x60);
      var s19 := Dup4(s18);
      var s20 := Add(s19);
      var s21 := Dup6(s20);
      assert s21.Peek(2) == 0x50c;
      assert s21.Peek(8) == 0xd7;
      assert s21.Peek(14) == 0x7d;
      var s22 := Push2(s21, 0x049d);
      var s23 := Jump(s22);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s99(s23, gas - 1)
  }

  /** Node 99
    * Segment Id for this node is: 74
    * Starting at 0x49d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 16

    requires s0.stack[2] == 0x50c

    requires s0.stack[8] == 0xd7

    requires s0.stack[14] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x50c;
      assert s1.Peek(8) == 0xd7;
      assert s1.Peek(14) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s100(s8, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 75
    * Starting at 0x4a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x50c

    requires s0.stack[11] == 0xd7

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50c;
      assert s1.Peek(11) == 0xd7;
      assert s1.Peek(17) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04c3);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s102(s7, gas - 1)
      else
        ExecuteFromCFGNode_s101(s7, gas - 1)
  }

  /** Node 101
    * Segment Id for this node is: 76
    * Starting at 0x4b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x50c

    requires s0.stack[11] == 0xd7

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x50c;
      assert s1.Peek(12) == 0xd7;
      assert s1.Peek(18) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0x50c;
      assert s11.Peek(15) == 0xd7;
      assert s11.Peek(21) == 0x7d;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x04a7);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s100(s16, gas - 1)
  }

  /** Node 102
    * Segment Id for this node is: 77
    * Starting at 0x4c3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s102(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x50c

    requires s0.stack[11] == 0xd7

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50c;
      assert s1.Peek(11) == 0xd7;
      assert s1.Peek(17) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04d5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s104(s7, gas - 1)
      else
        ExecuteFromCFGNode_s103(s7, gas - 1)
  }

  /** Node 103
    * Segment Id for this node is: 78
    * Starting at 0x4cc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s103(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x50c

    requires s0.stack[11] == 0xd7

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x50c;
      assert s1.Peek(12) == 0xd7;
      assert s1.Peek(18) == 0x7d;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s104(s7, gas - 1)
  }

  /** Node 104
    * Segment Id for this node is: 79
    * Starting at 0x4d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s104(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x50c

    requires s0.stack[11] == 0xd7

    requires s0.stack[17] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x50c;
      assert s1.Peek(11) == 0xd7;
      assert s1.Peek(17) == 0x7d;
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
      assert s11.Peek(3) == 0x50c;
      assert s11.Peek(9) == 0xd7;
      assert s11.Peek(15) == 0x7d;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap3(s13);
      var s15 := Swap2(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s105(s18, gas - 1)
  }

  /** Node 105
    * Segment Id for this node is: 81
    * Starting at 0x50c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -6
    * Net Capacity Effect: +6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s105(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[6] == 0xd7

    requires s0.stack[12] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0xd7;
      assert s1.Peek(12) == 0x7d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup3(s3);
      var s5 := Push1(s4, 0x40);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Swap5(s8);
      var s10 := Swap4(s9);
      var s11 := Pop(s10);
      assert s11.Peek(3) == 0xd7;
      assert s11.Peek(10) == 0x7d;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s106(s15, gas - 1)
  }

  /** Node 106
    * Segment Id for this node is: 12
    * Starting at 0xd7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s106(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[6] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x7d;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Push1(s8, 0x00);
      var s10 := Dup8(s9);
      var s11 := Gas(s10);
      assert s11.Peek(13) == 0x7d;
      var s12 := Call(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x00f6);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s108(s17, gas - 1)
      else
        ExecuteFromCFGNode_s107(s17, gas - 1)
  }

  /** Node 107
    * Segment Id for this node is: 13
    * Starting at 0xed
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s107(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xed as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(8) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 108
    * Segment Id for this node is: 14
    * Starting at 0xf6
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s108(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xf6 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x7d;
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
      assert s11.Peek(7) == 0x7d;
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
      assert s21.Peek(6) == 0x7d;
      var s22 := Add(s21);
      var s23 := Swap1(s22);
      var s24 := Push2(s23, 0x011a);
      var s25 := Swap2(s24);
      var s26 := Swap1(s25);
      var s27 := Push2(s26, 0x051c);
      var s28 := Jump(s27);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s109(s28, gas - 1)
  }

  /** Node 109
    * Segment Id for this node is: 82
    * Starting at 0x51c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s109(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x51c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x11a

    requires s0.stack[6] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x11a;
      assert s1.Peek(6) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x052e);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s111(s10, gas - 1)
      else
        ExecuteFromCFGNode_s110(s10, gas - 1)
  }

  /** Node 110
    * Segment Id for this node is: 83
    * Starting at 0x52a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s110(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11a

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x11a;
      assert s1.Peek(8) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 111
    * Segment Id for this node is: 84
    * Starting at 0x52e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s111(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x52e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x11a

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x11a;
      assert s1.Peek(7) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Push2(s3, 0x0539);
      var s5 := Dup2(s4);
      var s6 := Push2(s5, 0x0245);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s112(s7, gas - 1)
  }

  /** Node 112
    * Segment Id for this node is: 29
    * Starting at 0x245
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s112(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x245 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x539

    requires s0.stack[6] == 0x11a

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x539;
      assert s1.Peek(6) == 0x11a;
      assert s1.Peek(10) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := And(s7);
      var s9 := Dup2(s8);
      var s10 := Eq(s9);
      var s11 := Push2(s10, 0x025a);
      assert s11.Peek(0) == 0x25a;
      assert s11.Peek(3) == 0x539;
      assert s11.Peek(8) == 0x11a;
      assert s11.Peek(12) == 0x7d;
      var s12 := JumpI(s11);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s11.stack[1] > 0 then
        ExecuteFromCFGNode_s114(s12, gas - 1)
      else
        ExecuteFromCFGNode_s113(s12, gas - 1)
  }

  /** Node 113
    * Segment Id for this node is: 30
    * Starting at 0x256
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s113(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x256 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x539

    requires s0.stack[6] == 0x11a

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x539;
      assert s1.Peek(7) == 0x11a;
      assert s1.Peek(11) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 114
    * Segment Id for this node is: 31
    * Starting at 0x25a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s114(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x25a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[1] == 0x539

    requires s0.stack[6] == 0x11a

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x539;
      assert s1.Peek(6) == 0x11a;
      assert s1.Peek(10) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s115(s3, gas - 1)
  }

  /** Node 115
    * Segment Id for this node is: 85
    * Starting at 0x539
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s115(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x539 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x11a

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x11a;
      assert s1.Peek(8) == 0x7d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s116(s7, gas - 1)
  }

  /** Node 116
    * Segment Id for this node is: 15
    * Starting at 0x11a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +6
    * Net Capacity Effect: -6
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s116(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x11a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0x01);
      var s7 := Push1(s6, 0xa0);
      var s8 := Shl(s7);
      var s9 := Sub(s8);
      var s10 := And(s9);
      var s11 := Push4(s10, 0x6a761202);
      assert s11.Peek(5) == 0x7d;
      var s12 := CallValue(s11);
      var s13 := Dup5(s12);
      var s14 := Push1(s13, 0x00);
      var s15 := Add(s14);
      var s16 := MLoad(s15);
      var s17 := Dup6(s16);
      var s18 := Push1(s17, 0x20);
      var s19 := Add(s18);
      var s20 := MLoad(s19);
      var s21 := Dup7(s20);
      assert s21.Peek(9) == 0x7d;
      var s22 := Push1(s21, 0x40);
      var s23 := Add(s22);
      var s24 := MLoad(s23);
      var s25 := Dup8(s24);
      var s26 := Push1(s25, 0x60);
      var s27 := Add(s26);
      var s28 := MLoad(s27);
      var s29 := Push1(s28, 0xff);
      var s30 := And(s29);
      var s31 := Push1(s30, 0x01);
      assert s31.Peek(11) == 0x7d;
      var s32 := Dup2(s31);
      var s33 := Gt(s32);
      var s34 := IsZero(s33);
      var s35 := Push2(s34, 0x0154);
      var s36 := JumpI(s35);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s35.stack[1] > 0 then
        ExecuteFromCFGNode_s119(s36, gas - 1)
      else
        ExecuteFromCFGNode_s117(s36, gas - 1)
  }

  /** Node 117
    * Segment Id for this node is: 16
    * Starting at 0x14d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s117(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x14d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0154);
      assert s1.Peek(0) == 0x154;
      assert s1.Peek(11) == 0x7d;
      var s2 := Push2(s1, 0x0540);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s118(s3, gas - 1)
  }

  /** Node 118
    * Segment Id for this node is: 86
    * Starting at 0x540
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s118(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x540 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[0] == 0x154

    requires s0.stack[11] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x154;
      assert s1.Peek(11) == 0x7d;
      var s2 := Push4(s1, 0x4e487b71);
      var s3 := Push1(s2, 0xe0);
      var s4 := Shl(s3);
      var s5 := Push1(s4, 0x00);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x21);
      var s8 := Push1(s7, 0x04);
      var s9 := MStore(s8);
      var s10 := Push1(s9, 0x24);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(2) == 0x154;
      assert s11.Peek(13) == 0x7d;
      var s12 := Revert(s11);
      // Segment is terminal (Revert, Stop or Return)
      s12
  }

  /** Node 119
    * Segment Id for this node is: 17
    * Starting at 0x154
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 9
    * Minimum capacity for this segment to prevent stack overflow: 9
    * Net Stack Effect: +8
    * Net Capacity Effect: -8
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s119(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x154 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[10] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(10) == 0x7d;
      var s2 := Dup9(s1);
      var s3 := Push1(s2, 0x80);
      var s4 := Add(s3);
      var s5 := MLoad(s4);
      var s6 := Dup10(s5);
      var s7 := Push1(s6, 0xa0);
      var s8 := Add(s7);
      var s9 := MLoad(s8);
      var s10 := Dup11(s9);
      var s11 := Push1(s10, 0xc0);
      assert s11.Peek(14) == 0x7d;
      var s12 := Add(s11);
      var s13 := MLoad(s12);
      var s14 := Dup12(s13);
      var s15 := Push1(s14, 0xe0);
      var s16 := Add(s15);
      var s17 := MLoad(s16);
      var s18 := Dup13(s17);
      var s19 := Push2(s18, 0x0100);
      var s20 := Add(s19);
      var s21 := MLoad(s20);
      assert s21.Peek(15) == 0x7d;
      var s22 := Dup14(s21);
      var s23 := Push2(s22, 0x0120);
      var s24 := Add(s23);
      var s25 := MLoad(s24);
      var s26 := Push1(s25, 0x40);
      var s27 := MLoad(s26);
      var s28 := Dup13(s27);
      var s29 := Push4(s28, 0xffffffff);
      var s30 := And(s29);
      var s31 := Push1(s30, 0xe0);
      assert s31.Peek(19) == 0x7d;
      var s32 := Shl(s31);
      var s33 := Dup2(s32);
      var s34 := MStore(s33);
      var s35 := Push1(s34, 0x04);
      var s36 := Add(s35);
      var s37 := Push2(s36, 0x0199);
      var s38 := Swap(s37, 11);
      var s39 := Swap(s38, 10);
      var s40 := Swap(s39, 9);
      var s41 := Swap(s40, 8);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s120(s41, gas - 1)
  }

  /** Node 120
    * Segment Id for this node is: 18
    * Starting at 0x18e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s120(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[11] == 0x199

    requires s0.stack[18] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Swap7(s0);
      assert s1.Peek(11) == 0x199;
      assert s1.Peek(18) == 0x7d;
      var s2 := Swap6(s1);
      var s3 := Swap5(s2);
      var s4 := Swap4(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Push2(s7, 0x0556);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s121(s9, gas - 1)
  }

  /** Node 121
    * Segment Id for this node is: 87
    * Starting at 0x556
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s121(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x556 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[11] == 0x199

    requires s0.stack[18] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(11) == 0x199;
      assert s1.Peek(18) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0140);
      var s4 := Push1(s3, 0x01);
      var s5 := Push1(s4, 0x01);
      var s6 := Push1(s5, 0xa0);
      var s7 := Shl(s6);
      var s8 := Sub(s7);
      var s9 := Dup14(s8);
      var s10 := And(s9);
      var s11 := Dup4(s10);
      assert s11.Peek(15) == 0x199;
      assert s11.Peek(22) == 0x7d;
      var s12 := MStore(s11);
      var s13 := Dup12(s12);
      var s14 := Push1(s13, 0x20);
      var s15 := Dup5(s14);
      var s16 := Add(s15);
      var s17 := MStore(s16);
      var s18 := Dup1(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := Dup5(s19);
      var s21 := Add(s20);
      assert s21.Peek(15) == 0x199;
      assert s21.Peek(22) == 0x7d;
      var s22 := MStore(s21);
      var s23 := Push2(s22, 0x057f);
      var s24 := Dup2(s23);
      var s25 := Dup5(s24);
      var s26 := Add(s25);
      var s27 := Dup13(s26);
      var s28 := Push2(s27, 0x049d);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s122(s29, gas - 1)
  }

  /** Node 122
    * Segment Id for this node is: 74
    * Starting at 0x49d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s122(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x57f

    requires s0.stack[16] == 0x199

    requires s0.stack[23] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x57f;
      assert s1.Peek(16) == 0x199;
      assert s1.Peek(23) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s123(s8, gas - 1)
  }

  /** Node 123
    * Segment Id for this node is: 75
    * Starting at 0x4a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s123(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x57f

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x57f;
      assert s1.Peek(19) == 0x199;
      assert s1.Peek(26) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04c3);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s125(s7, gas - 1)
      else
        ExecuteFromCFGNode_s124(s7, gas - 1)
  }

  /** Node 124
    * Segment Id for this node is: 76
    * Starting at 0x4b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s124(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x57f

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x57f;
      assert s1.Peek(20) == 0x199;
      assert s1.Peek(27) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0x57f;
      assert s11.Peek(23) == 0x199;
      assert s11.Peek(30) == 0x7d;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x04a7);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s123(s16, gas - 1)
  }

  /** Node 125
    * Segment Id for this node is: 77
    * Starting at 0x4c3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s125(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x57f

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x57f;
      assert s1.Peek(19) == 0x199;
      assert s1.Peek(26) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04d5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s127(s7, gas - 1)
      else
        ExecuteFromCFGNode_s126(s7, gas - 1)
  }

  /** Node 126
    * Segment Id for this node is: 78
    * Starting at 0x4cc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s126(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x57f

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x57f;
      assert s1.Peek(20) == 0x199;
      assert s1.Peek(27) == 0x7d;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s127(s7, gas - 1)
  }

  /** Node 127
    * Segment Id for this node is: 79
    * Starting at 0x4d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s127(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x57f

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x57f;
      assert s1.Peek(19) == 0x199;
      assert s1.Peek(26) == 0x7d;
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
      assert s11.Peek(3) == 0x57f;
      assert s11.Peek(17) == 0x199;
      assert s11.Peek(24) == 0x7d;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap3(s13);
      var s15 := Swap2(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s128(s18, gas - 1)
  }

  /** Node 128
    * Segment Id for this node is: 88
    * Starting at 0x57f
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 11
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s128(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x57f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[14] == 0x199

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x199;
      assert s1.Peek(21) == 0x7d;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Push1(s3, 0x02);
      var s5 := Dup11(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x059f);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s130(s8, gas - 1)
      else
        ExecuteFromCFGNode_s129(s8, gas - 1)
  }

  /** Node 129
    * Segment Id for this node is: 89
    * Starting at 0x58a
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s129(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x58a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[13] == 0x199

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push4(s0, 0x4e487b71);
      assert s1.Peek(14) == 0x199;
      assert s1.Peek(21) == 0x7d;
      var s2 := Push1(s1, 0xe0);
      var s3 := Shl(s2);
      var s4 := Push1(s3, 0x00);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x21);
      var s7 := Push1(s6, 0x04);
      var s8 := MStore(s7);
      var s9 := Push1(s8, 0x24);
      var s10 := Push1(s9, 0x00);
      var s11 := Revert(s10);
      // Segment is terminal (Revert, Stop or Return)
      s11
  }

  /** Node 130
    * Segment Id for this node is: 90
    * Starting at 0x59f
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 10
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s130(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x59f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[13] == 0x199

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x199;
      assert s1.Peek(20) == 0x7d;
      var s2 := Dup10(s1);
      var s3 := Push1(s2, 0x60);
      var s4 := Dup5(s3);
      var s5 := Add(s4);
      var s6 := MStore(s5);
      var s7 := Dup9(s6);
      var s8 := Push1(s7, 0x80);
      var s9 := Dup5(s8);
      var s10 := Add(s9);
      var s11 := MStore(s10);
      assert s11.Peek(13) == 0x199;
      assert s11.Peek(20) == 0x7d;
      var s12 := Dup8(s11);
      var s13 := Push1(s12, 0xa0);
      var s14 := Dup5(s13);
      var s15 := Add(s14);
      var s16 := MStore(s15);
      var s17 := Dup7(s16);
      var s18 := Push1(s17, 0xc0);
      var s19 := Dup5(s18);
      var s20 := Add(s19);
      var s21 := MStore(s20);
      assert s21.Peek(13) == 0x199;
      assert s21.Peek(20) == 0x7d;
      var s22 := Push2(s21, 0x05cc);
      var s23 := Push1(s22, 0xe0);
      var s24 := Dup5(s23);
      var s25 := Add(s24);
      var s26 := Dup8(s25);
      var s27 := Push1(s26, 0x01);
      var s28 := Push1(s27, 0x01);
      var s29 := Push1(s28, 0xa0);
      var s30 := Shl(s29);
      var s31 := Sub(s30);
      assert s31.Peek(3) == 0x5cc;
      assert s31.Peek(17) == 0x199;
      assert s31.Peek(24) == 0x7d;
      var s32 := And(s31);
      var s33 := Swap1(s32);
      var s34 := MStore(s33);
      var s35 := Jump(s34);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s131(s35, gas - 1)
  }

  /** Node 131
    * Segment Id for this node is: 91
    * Starting at 0x5cc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s131(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[13] == 0x199

    requires s0.stack[20] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(13) == 0x199;
      assert s1.Peek(20) == 0x7d;
      var s2 := Push1(s1, 0x01);
      var s3 := Push1(s2, 0x01);
      var s4 := Push1(s3, 0xa0);
      var s5 := Shl(s4);
      var s6 := Sub(s5);
      var s7 := Dup6(s6);
      var s8 := And(s7);
      var s9 := Push2(s8, 0x0100);
      var s10 := Dup5(s9);
      var s11 := Add(s10);
      assert s11.Peek(15) == 0x199;
      assert s11.Peek(22) == 0x7d;
      var s12 := MStore(s11);
      var s13 := Dup3(s12);
      var s14 := Dup2(s13);
      var s15 := Sub(s14);
      var s16 := Push2(s15, 0x0120);
      var s17 := Dup5(s16);
      var s18 := Add(s17);
      var s19 := MStore(s18);
      var s20 := Push2(s19, 0x05ef);
      var s21 := Dup2(s20);
      assert s21.Peek(1) == 0x5ef;
      assert s21.Peek(15) == 0x199;
      assert s21.Peek(22) == 0x7d;
      var s22 := Dup6(s21);
      var s23 := Push2(s22, 0x049d);
      var s24 := Jump(s23);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s132(s24, gas - 1)
  }

  /** Node 132
    * Segment Id for this node is: 74
    * Starting at 0x49d
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s132(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x49d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x5ef

    requires s0.stack[16] == 0x199

    requires s0.stack[23] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x5ef;
      assert s1.Peek(16) == 0x199;
      assert s1.Peek(23) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup5(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s133(s8, gas - 1)
  }

  /** Node 133
    * Segment Id for this node is: 75
    * Starting at 0x4a7
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s133(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x5ef

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5ef;
      assert s1.Peek(19) == 0x199;
      assert s1.Peek(26) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04c3);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s135(s7, gas - 1)
      else
        ExecuteFromCFGNode_s134(s7, gas - 1)
  }

  /** Node 134
    * Segment Id for this node is: 76
    * Starting at 0x4b0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s134(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4b0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x5ef

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x20);
      assert s1.Peek(6) == 0x5ef;
      assert s1.Peek(20) == 0x199;
      assert s1.Peek(27) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup6(s2);
      var s4 := Add(s3);
      var s5 := Dup2(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Dup7(s7);
      var s9 := Dup4(s8);
      var s10 := Add(s9);
      var s11 := Dup3(s10);
      assert s11.Peek(9) == 0x5ef;
      assert s11.Peek(23) == 0x199;
      assert s11.Peek(30) == 0x7d;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Add(s13);
      var s15 := Push2(s14, 0x04a7);
      var s16 := Jump(s15);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s133(s16, gas - 1)
  }

  /** Node 135
    * Segment Id for this node is: 77
    * Starting at 0x4c3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s135(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4c3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x5ef

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5ef;
      assert s1.Peek(19) == 0x199;
      assert s1.Peek(26) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := Gt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x04d5);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s137(s7, gas - 1)
      else
        ExecuteFromCFGNode_s136(s7, gas - 1)
  }

  /** Node 136
    * Segment Id for this node is: 78
    * Starting at 0x4cc
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s136(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x5ef

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x5ef;
      assert s1.Peek(20) == 0x199;
      assert s1.Peek(27) == 0x7d;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup4(s2);
      var s4 := Dup8(s3);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MStore(s6);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s137(s7, gas - 1)
  }

  /** Node 137
    * Segment Id for this node is: 79
    * Starting at 0x4d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s137(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[5] == 0x5ef

    requires s0.stack[19] == 0x199

    requires s0.stack[26] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x5ef;
      assert s1.Peek(19) == 0x199;
      assert s1.Peek(26) == 0x7d;
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
      assert s11.Peek(3) == 0x5ef;
      assert s11.Peek(17) == 0x199;
      assert s11.Peek(24) == 0x7d;
      var s12 := Push1(s11, 0x20);
      var s13 := Add(s12);
      var s14 := Swap3(s13);
      var s15 := Swap2(s14);
      var s16 := Pop(s15);
      var s17 := Pop(s16);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s138(s18, gas - 1)
  }

  /** Node 138
    * Segment Id for this node is: 92
    * Starting at 0x5ef
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 15
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -14
    * Net Capacity Effect: +14
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s138(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x5ef as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[14] == 0x199

    requires s0.stack[21] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(14) == 0x199;
      assert s1.Peek(21) == 0x7d;
      var s2 := Swap(s1, 14);
      var s3 := Swap(s2, 13);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Pop(s9);
      var s11 := Pop(s10);
      assert s11.Peek(5) == 0x199;
      assert s11.Peek(13) == 0x7d;
      var s12 := Pop(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Pop(s14);
      var s16 := Pop(s15);
      var s17 := Jump(s16);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s139(s17, gas - 1)
  }

  /** Node 139
    * Segment Id for this node is: 19
    * Starting at 0x199
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s139(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x199 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x7d;
      var s2 := Push1(s1, 0x20);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Dup1(s4);
      var s6 := Dup4(s5);
      var s7 := Sub(s6);
      var s8 := Dup2(s7);
      var s9 := Dup6(s8);
      var s10 := Dup9(s9);
      var s11 := Gas(s10);
      assert s11.Peek(14) == 0x7d;
      var s12 := Call(s11);
      var s13 := IsZero(s12);
      var s14 := Dup1(s13);
      var s15 := IsZero(s14);
      var s16 := Push2(s15, 0x01b7);
      var s17 := JumpI(s16);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s16.stack[1] > 0 then
        ExecuteFromCFGNode_s141(s17, gas - 1)
      else
        ExecuteFromCFGNode_s140(s17, gas - 1)
  }

  /** Node 140
    * Segment Id for this node is: 20
    * Starting at 0x1ae
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s140(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(9) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := ReturnDataCopy(s3);
      var s5 := ReturnDataSize(s4);
      var s6 := Push1(s5, 0x00);
      var s7 := Revert(s6);
      // Segment is terminal (Revert, Stop or Return)
      s7
  }

  /** Node 141
    * Segment Id for this node is: 21
    * Starting at 0x1b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s141(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(8) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x40);
      var s8 := MLoad(s7);
      var s9 := ReturnDataSize(s8);
      var s10 := Push1(s9, 0x1f);
      var s11 := Not(s10);
      assert s11.Peek(6) == 0x7d;
      var s12 := Push1(s11, 0x1f);
      var s13 := Dup3(s12);
      var s14 := Add(s13);
      var s15 := And(s14);
      var s16 := Dup3(s15);
      var s17 := Add(s16);
      var s18 := Dup1(s17);
      var s19 := Push1(s18, 0x40);
      var s20 := MStore(s19);
      var s21 := Pop(s20);
      assert s21.Peek(5) == 0x7d;
      var s22 := Dup2(s21);
      var s23 := Add(s22);
      var s24 := Swap1(s23);
      var s25 := Push2(s24, 0x01dc);
      var s26 := Swap2(s25);
      var s27 := Swap1(s26);
      var s28 := Push2(s27, 0x0600);
      var s29 := Jump(s28);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s142(s29, gas - 1)
  }

  /** Node 142
    * Segment Id for this node is: 93
    * Starting at 0x600
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s142(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x600 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[2] == 0x1dc

    requires s0.stack[6] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1dc;
      assert s1.Peek(6) == 0x7d;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Dup5(s4);
      var s6 := Sub(s5);
      var s7 := SLt(s6);
      var s8 := IsZero(s7);
      var s9 := Push2(s8, 0x0612);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s144(s10, gas - 1)
      else
        ExecuteFromCFGNode_s143(s10, gas - 1)
  }

  /** Node 143
    * Segment Id for this node is: 94
    * Starting at 0x60e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s143(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x60e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1dc

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x1dc;
      assert s1.Peek(8) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 144
    * Segment Id for this node is: 95
    * Starting at 0x612
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s144(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x612 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[3] == 0x1dc

    requires s0.stack[7] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1dc;
      assert s1.Peek(7) == 0x7d;
      var s2 := Dup2(s1);
      var s3 := MLoad(s2);
      var s4 := Dup1(s3);
      var s5 := IsZero(s4);
      var s6 := IsZero(s5);
      var s7 := Dup2(s6);
      var s8 := Eq(s7);
      var s9 := Push2(s8, 0x0539);
      var s10 := JumpI(s9);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s9.stack[1] > 0 then
        ExecuteFromCFGNode_s146(s10, gas - 1)
      else
        ExecuteFromCFGNode_s145(s10, gas - 1)
  }

  /** Node 145
    * Segment Id for this node is: 96
    * Starting at 0x61e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s145(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x61e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1dc

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x1dc;
      assert s1.Peek(9) == 0x7d;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 146
    * Segment Id for this node is: 85
    * Starting at 0x539
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s146(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x539 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[4] == 0x1dc

    requires s0.stack[8] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x1dc;
      assert s1.Peek(8) == 0x7d;
      var s2 := Swap4(s1);
      var s3 := Swap3(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s147(s7, gas - 1)
  }

  /** Node 147
    * Segment Id for this node is: 22
    * Starting at 0x1dc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s147(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1dc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x7d

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x7d;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s148(s6, gas - 1)
  }

  /** Node 148
    * Segment Id for this node is: 10
    * Starting at 0x7d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s148(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x7d as nat
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

  /** Node 149
    * Segment Id for this node is: 4
    * Starting at 0x2e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s149(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e as nat
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
      var s5 := Push2(s4, 0x003a);
      var s6 := JumpI(s5);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s5.stack[1] > 0 then
        ExecuteFromCFGNode_s151(s6, gas - 1)
      else
        ExecuteFromCFGNode_s150(s6, gas - 1)
  }

  /** Node 150
    * Segment Id for this node is: 5
    * Starting at 0x36
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s150(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x36 as nat
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

  /** Node 151
    * Segment Id for this node is: 6
    * Starting at 0x3a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s151(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 2

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Pop(s1);
      var s3 := Push1(s2, 0x00);
      var s4 := SLoad(s3);
      var s5 := Push2(s4, 0x004e);
      var s6 := Swap1(s5);
      var s7 := Push1(s6, 0x01);
      var s8 := Push1(s7, 0x01);
      var s9 := Push1(s8, 0xa0);
      var s10 := Shl(s9);
      var s11 := Sub(s10);
      assert s11.Peek(2) == 0x4e;
      var s12 := And(s11);
      var s13 := Dup2(s12);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s152(s14, gas - 1)
  }

  /** Node 152
    * Segment Id for this node is: 7
    * Starting at 0x4e
    * Segment type is: RETURN Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s152(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 3

    requires s0.stack[1] == 0x4e

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4e;
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
      assert s11.Peek(2) == 0x4e;
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
      assert s21.Peek(2) == 0x4e;
      var s22 := Return(s21);
      // Segment is terminal (Revert, Stop or Return)
      s22
  }

  /** Node 153
    * Segment Id for this node is: 3
    * Starting at 0x29
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s153(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29 as nat
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
