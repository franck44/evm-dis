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
      var s7 := Push2(s6, 0x0022);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s99(s8, gas - 1)
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
      var s6 := Push4(s5, 0xffc3a769);
      var s7 := Eq(s6);
      var s8 := Push2(s7, 0x002e);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s4(s9, gas - 1)
      else
        ExecuteFromCFGNode_s2(s9, gas - 1)
  }

  /** Node 2
    * Segment Id for this node is: 2
    * Starting at 0x1e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
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
      var s1 := Push2(s0, 0x0029);
      assert s1.Peek(0) == 0x29;
      var s2 := Jump(s1);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s3(s2, gas - 1)
  }

  /** Node 3
    * Segment Id for this node is: 5
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
    * Segment Id for this node is: 6
    * Starting at 0x2e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s4(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 1

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := Push2(s1, 0x0048);
      var s3 := Push1(s2, 0x04);
      var s4 := Dup1(s3);
      var s5 := CallDataSize(s4);
      var s6 := Sub(s5);
      var s7 := Dup2(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x0043);
      var s11 := Swap2(s10);
      assert s11.Peek(2) == 0x43;
      assert s11.Peek(3) == 0x48;
      var s12 := Swap1(s11);
      var s13 := Push2(s12, 0x02cf);
      var s14 := Jump(s13);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s5(s14, gas - 1)
  }

  /** Node 5
    * Segment Id for this node is: 53
    * Starting at 0x2cf
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s5(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2cf as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[2] == 0x43

    requires s0.stack[3] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x43;
      assert s1.Peek(3) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup1(s2);
      var s4 := Push1(s3, 0x40);
      var s5 := Dup4(s4);
      var s6 := Dup6(s5);
      var s7 := Sub(s6);
      var s8 := SLt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x02e2);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s7(s11, gas - 1)
      else
        ExecuteFromCFGNode_s6(s11, gas - 1)
  }

  /** Node 6
    * Segment Id for this node is: 54
    * Starting at 0x2de
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s6(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2de as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x43

    requires s0.stack[5] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(5) == 0x43;
      assert s1.Peek(6) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 7
    * Segment Id for this node is: 55
    * Starting at 0x2e2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s7(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2e2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[4] == 0x43

    requires s0.stack[5] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x43;
      assert s1.Peek(5) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup4(s2);
      var s4 := Add(s3);
      var s5 := CallDataLoad(s4);
      var s6 := Push8(s5, 0xffffffffffffffff);
      var s7 := Dup2(s6);
      var s8 := Gt(s7);
      var s9 := IsZero(s8);
      var s10 := Push2(s9, 0x02fc);
      var s11 := JumpI(s10);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s10.stack[1] > 0 then
        ExecuteFromCFGNode_s9(s11, gas - 1)
      else
        ExecuteFromCFGNode_s8(s11, gas - 1)
  }

  /** Node 8
    * Segment Id for this node is: 56
    * Starting at 0x2f8
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s8(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x43

    requires s0.stack[6] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x43;
      assert s1.Peek(7) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 9
    * Segment Id for this node is: 57
    * Starting at 0x2fc
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s9(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2fc as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x43

    requires s0.stack[6] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x43;
      assert s1.Peek(6) == 0x48;
      var s2 := Push2(s1, 0x0308);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0266);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s10(s8, gas - 1)
  }

  /** Node 10
    * Segment Id for this node is: 43
    * Starting at 0x266
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s10(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x266 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x308

    requires s0.stack[8] == 0x43

    requires s0.stack[9] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x308;
      assert s1.Peek(8) == 0x43;
      assert s1.Peek(9) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x0277);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s12(s9, gas - 1)
      else
        ExecuteFromCFGNode_s11(s9, gas - 1)
  }

  /** Node 11
    * Segment Id for this node is: 44
    * Starting at 0x273
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s11(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x273 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x308

    requires s0.stack[9] == 0x43

    requires s0.stack[10] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x308;
      assert s1.Peek(10) == 0x43;
      assert s1.Peek(11) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 12
    * Segment Id for this node is: 45
    * Starting at 0x277
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s12(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x277 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x308

    requires s0.stack[9] == 0x43

    requires s0.stack[10] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x308;
      assert s1.Peek(9) == 0x43;
      assert s1.Peek(10) == 0x48;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x0287);
      var s5 := Dup5(s4);
      var s6 := Dup3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x0179);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s13(s11, gas - 1)
  }

  /** Node 13
    * Segment Id for this node is: 23
    * Starting at 0x179
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s13(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x179 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x287

    requires s0.stack[8] == 0x308

    requires s0.stack[14] == 0x43

    requires s0.stack[15] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x287;
      assert s1.Peek(8) == 0x308;
      assert s1.Peek(14) == 0x43;
      assert s1.Peek(15) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x018c);
      var s4 := Push2(s3, 0x0187);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x03f2);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s14(s7, gas - 1)
  }

  /** Node 14
    * Segment Id for this node is: 70
    * Starting at 0x3f2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s14(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3f2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x187

    requires s0.stack[2] == 0x18c

    requires s0.stack[7] == 0x287

    requires s0.stack[12] == 0x308

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x187;
      assert s1.Peek(2) == 0x18c;
      assert s1.Peek(7) == 0x287;
      assert s1.Peek(12) == 0x308;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x040d);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s17(s8, gas - 1)
      else
        ExecuteFromCFGNode_s15(s8, gas - 1)
  }

  /** Node 15
    * Segment Id for this node is: 71
    * Starting at 0x405
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s15(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x405 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x187

    requires s0.stack[3] == 0x18c

    requires s0.stack[8] == 0x287

    requires s0.stack[13] == 0x308

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x040c);
      assert s1.Peek(0) == 0x40c;
      assert s1.Peek(3) == 0x187;
      assert s1.Peek(4) == 0x18c;
      assert s1.Peek(9) == 0x287;
      assert s1.Peek(14) == 0x308;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
      var s2 := Push2(s1, 0x050f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s16(s3, gas - 1)
  }

  /** Node 16
    * Segment Id for this node is: 89
    * Starting at 0x50f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s16(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x40c

    requires s0.stack[3] == 0x187

    requires s0.stack[4] == 0x18c

    requires s0.stack[9] == 0x287

    requires s0.stack[14] == 0x308

    requires s0.stack[20] == 0x43

    requires s0.stack[21] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x40c;
      assert s1.Peek(3) == 0x187;
      assert s1.Peek(4) == 0x18c;
      assert s1.Peek(9) == 0x287;
      assert s1.Peek(14) == 0x308;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
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

  /** Node 17
    * Segment Id for this node is: 73
    * Starting at 0x40d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s17(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x40d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x187

    requires s0.stack[3] == 0x18c

    requires s0.stack[8] == 0x287

    requires s0.stack[13] == 0x308

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x187;
      assert s1.Peek(3) == 0x18c;
      assert s1.Peek(8) == 0x287;
      assert s1.Peek(13) == 0x308;
      assert s1.Peek(19) == 0x43;
      assert s1.Peek(20) == 0x48;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x187;
      assert s11.Peek(3) == 0x18c;
      assert s11.Peek(8) == 0x287;
      assert s11.Peek(13) == 0x308;
      assert s11.Peek(19) == 0x43;
      assert s11.Peek(20) == 0x48;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s18(s15, gas - 1)
  }

  /** Node 18
    * Segment Id for this node is: 24
    * Starting at 0x187
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s18(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x187 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x18c

    requires s0.stack[6] == 0x287

    requires s0.stack[11] == 0x308

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18c;
      assert s1.Peek(6) == 0x287;
      assert s1.Peek(11) == 0x308;
      assert s1.Peek(17) == 0x43;
      assert s1.Peek(18) == 0x48;
      var s2 := Push2(s1, 0x03c1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s19(s3, gas - 1)
  }

  /** Node 19
    * Segment Id for this node is: 66
    * Starting at 0x3c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s19(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x18c

    requires s0.stack[6] == 0x287

    requires s0.stack[11] == 0x308

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x18c;
      assert s1.Peek(6) == 0x287;
      assert s1.Peek(11) == 0x308;
      assert s1.Peek(17) == 0x43;
      assert s1.Peek(18) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x18c;
      assert s11.Peek(10) == 0x287;
      assert s11.Peek(15) == 0x308;
      assert s11.Peek(21) == 0x43;
      assert s11.Peek(22) == 0x48;
      var s12 := Lt(s11);
      var s13 := Push8(s12, 0xffffffffffffffff);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := Push2(s17, 0x03e8);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s22(s19, gas - 1)
      else
        ExecuteFromCFGNode_s20(s19, gas - 1)
  }

  /** Node 20
    * Segment Id for this node is: 67
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s20(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x18c

    requires s0.stack[8] == 0x287

    requires s0.stack[13] == 0x308

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03e7);
      assert s1.Peek(0) == 0x3e7;
      assert s1.Peek(4) == 0x18c;
      assert s1.Peek(9) == 0x287;
      assert s1.Peek(14) == 0x308;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
      var s2 := Push2(s1, 0x050f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s21(s3, gas - 1)
  }

  /** Node 21
    * Segment Id for this node is: 89
    * Starting at 0x50f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s21(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x3e7

    requires s0.stack[4] == 0x18c

    requires s0.stack[9] == 0x287

    requires s0.stack[14] == 0x308

    requires s0.stack[20] == 0x43

    requires s0.stack[21] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3e7;
      assert s1.Peek(4) == 0x18c;
      assert s1.Peek(9) == 0x287;
      assert s1.Peek(14) == 0x308;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
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

  /** Node 22
    * Segment Id for this node is: 69
    * Starting at 0x3e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s22(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x18c

    requires s0.stack[8] == 0x287

    requires s0.stack[13] == 0x308

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x18c;
      assert s1.Peek(8) == 0x287;
      assert s1.Peek(13) == 0x308;
      assert s1.Peek(19) == 0x43;
      assert s1.Peek(20) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s23(s9, gas - 1)
  }

  /** Node 23
    * Segment Id for this node is: 25
    * Starting at 0x18c
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s23(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x18c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x287

    requires s0.stack[10] == 0x308

    requires s0.stack[16] == 0x43

    requires s0.stack[17] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x287;
      assert s1.Peek(10) == 0x308;
      assert s1.Peek(16) == 0x43;
      assert s1.Peek(17) == 0x48;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x287;
      assert s11.Peek(11) == 0x308;
      assert s11.Peek(17) == 0x43;
      assert s11.Peek(18) == 0x48;
      var s12 := Pop(s11);
      var s13 := Dup3(s12);
      var s14 := Dup6(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup7(s15);
      var s17 := Mul(s16);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x287;
      assert s21.Peek(12) == 0x308;
      assert s21.Peek(18) == 0x43;
      assert s21.Peek(19) == 0x48;
      var s22 := Push2(s21, 0x01ab);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s25(s23, gas - 1)
      else
        ExecuteFromCFGNode_s24(s23, gas - 1)
  }

  /** Node 24
    * Segment Id for this node is: 26
    * Starting at 0x1a7
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s24(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1a7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x287

    requires s0.stack[11] == 0x308

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x287;
      assert s1.Peek(12) == 0x308;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 25
    * Segment Id for this node is: 27
    * Starting at 0x1ab
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s25(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ab as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x287

    requires s0.stack[11] == 0x308

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x287;
      assert s1.Peek(11) == 0x308;
      assert s1.Peek(17) == 0x43;
      assert s1.Peek(18) == 0x48;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s26(s2, gas - 1)
  }

  /** Node 26
    * Segment Id for this node is: 28
    * Starting at 0x1ae
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s26(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1ae as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x287

    requires s0.stack[12] == 0x308

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x287;
      assert s1.Peek(12) == 0x308;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Dup6(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x01db);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s38(s7, gas - 1)
      else
        ExecuteFromCFGNode_s27(s7, gas - 1)
  }

  /** Node 27
    * Segment Id for this node is: 29
    * Starting at 0x1b7
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s27(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1b7 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x287

    requires s0.stack[12] == 0x308

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(8) == 0x287;
      assert s1.Peek(13) == 0x308;
      assert s1.Peek(19) == 0x43;
      assert s1.Peek(20) == 0x48;
      var s2 := Push2(s1, 0x01c1);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x0251);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s28(s6, gas - 1)
  }

  /** Node 28
    * Segment Id for this node is: 41
    * Starting at 0x251
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s28(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x251 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x1c1

    requires s0.stack[11] == 0x287

    requires s0.stack[16] == 0x308

    requires s0.stack[22] == 0x43

    requires s0.stack[23] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1c1;
      assert s1.Peek(11) == 0x287;
      assert s1.Peek(16) == 0x308;
      assert s1.Peek(22) == 0x43;
      assert s1.Peek(23) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x0260);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x053e);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s29(s10, gas - 1)
  }

  /** Node 29
    * Segment Id for this node is: 90
    * Starting at 0x53e
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s29(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x53e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x260

    requires s0.stack[5] == 0x1c1

    requires s0.stack[14] == 0x287

    requires s0.stack[19] == 0x308

    requires s0.stack[25] == 0x43

    requires s0.stack[26] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(14) == 0x287;
      assert s1.Peek(19) == 0x308;
      assert s1.Peek(25) == 0x43;
      assert s1.Peek(26) == 0x48;
      var s2 := Push2(s1, 0x0547);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x045b);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s30(s5, gas - 1)
  }

  /** Node 30
    * Segment Id for this node is: 79
    * Starting at 0x45b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s30(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x45b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0x547

    requires s0.stack[3] == 0x260

    requires s0.stack[7] == 0x1c1

    requires s0.stack[16] == 0x287

    requires s0.stack[21] == 0x308

    requires s0.stack[27] == 0x43

    requires s0.stack[28] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x547;
      assert s1.Peek(3) == 0x260;
      assert s1.Peek(7) == 0x1c1;
      assert s1.Peek(16) == 0x287;
      assert s1.Peek(21) == 0x308;
      assert s1.Peek(27) == 0x43;
      assert s1.Peek(28) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0466);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x046d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s31(s6, gas - 1)
  }

  /** Node 31
    * Segment Id for this node is: 81
    * Starting at 0x46d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s31(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x46d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 33

    requires s0.stack[1] == 0x466

    requires s0.stack[4] == 0x547

    requires s0.stack[6] == 0x260

    requires s0.stack[10] == 0x1c1

    requires s0.stack[19] == 0x287

    requires s0.stack[24] == 0x308

    requires s0.stack[30] == 0x43

    requires s0.stack[31] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x466;
      assert s1.Peek(4) == 0x547;
      assert s1.Peek(6) == 0x260;
      assert s1.Peek(10) == 0x1c1;
      assert s1.Peek(19) == 0x287;
      assert s1.Peek(24) == 0x308;
      assert s1.Peek(30) == 0x43;
      assert s1.Peek(31) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push20(s2, 0xffffffffffffffffffffffffffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := And(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Swap2(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s32(s11, gas - 1)
  }

  /** Node 32
    * Segment Id for this node is: 80
    * Starting at 0x466
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s32(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x466 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 32

    requires s0.stack[3] == 0x547

    requires s0.stack[5] == 0x260

    requires s0.stack[9] == 0x1c1

    requires s0.stack[18] == 0x287

    requires s0.stack[23] == 0x308

    requires s0.stack[29] == 0x43

    requires s0.stack[30] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x547;
      assert s1.Peek(5) == 0x260;
      assert s1.Peek(9) == 0x1c1;
      assert s1.Peek(18) == 0x287;
      assert s1.Peek(23) == 0x308;
      assert s1.Peek(29) == 0x43;
      assert s1.Peek(30) == 0x48;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s33(s7, gas - 1)
  }

  /** Node 33
    * Segment Id for this node is: 91
    * Starting at 0x547
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s33(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x547 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x260

    requires s0.stack[6] == 0x1c1

    requires s0.stack[15] == 0x287

    requires s0.stack[20] == 0x308

    requires s0.stack[26] == 0x43

    requires s0.stack[27] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x260;
      assert s1.Peek(6) == 0x1c1;
      assert s1.Peek(15) == 0x287;
      assert s1.Peek(20) == 0x308;
      assert s1.Peek(26) == 0x43;
      assert s1.Peek(27) == 0x48;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0552);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s35(s5, gas - 1)
      else
        ExecuteFromCFGNode_s34(s5, gas - 1)
  }

  /** Node 34
    * Segment Id for this node is: 92
    * Starting at 0x54e
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s34(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x260

    requires s0.stack[5] == 0x1c1

    requires s0.stack[14] == 0x287

    requires s0.stack[19] == 0x308

    requires s0.stack[25] == 0x43

    requires s0.stack[26] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x260;
      assert s1.Peek(6) == 0x1c1;
      assert s1.Peek(15) == 0x287;
      assert s1.Peek(20) == 0x308;
      assert s1.Peek(26) == 0x43;
      assert s1.Peek(27) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 35
    * Segment Id for this node is: 93
    * Starting at 0x552
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s35(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x552 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x260

    requires s0.stack[5] == 0x1c1

    requires s0.stack[14] == 0x287

    requires s0.stack[19] == 0x308

    requires s0.stack[25] == 0x43

    requires s0.stack[26] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x260;
      assert s1.Peek(5) == 0x1c1;
      assert s1.Peek(14) == 0x287;
      assert s1.Peek(19) == 0x308;
      assert s1.Peek(25) == 0x43;
      assert s1.Peek(26) == 0x48;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s36(s3, gas - 1)
  }

  /** Node 36
    * Segment Id for this node is: 42
    * Starting at 0x260
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s36(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x260 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x1c1

    requires s0.stack[12] == 0x287

    requires s0.stack[17] == 0x308

    requires s0.stack[23] == 0x43

    requires s0.stack[24] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1c1;
      assert s1.Peek(12) == 0x287;
      assert s1.Peek(17) == 0x308;
      assert s1.Peek(23) == 0x43;
      assert s1.Peek(24) == 0x48;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s37(s6, gas - 1)
  }

  /** Node 37
    * Segment Id for this node is: 30
    * Starting at 0x1c1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s37(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x287

    requires s0.stack[14] == 0x308

    requires s0.stack[20] == 0x43

    requires s0.stack[21] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x287;
      assert s1.Peek(14) == 0x308;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(9) == 0x287;
      assert s11.Peek(14) == 0x308;
      assert s11.Peek(20) == 0x43;
      assert s11.Peek(21) == 0x48;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Pop(s18);
      var s20 := Push2(s19, 0x01ae);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s26(s21, gas - 1)
  }

  /** Node 38
    * Segment Id for this node is: 31
    * Starting at 0x1db
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s38(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1db as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x287

    requires s0.stack[12] == 0x308

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x287;
      assert s1.Peek(12) == 0x308;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s39(s10, gas - 1)
  }

  /** Node 39
    * Segment Id for this node is: 46
    * Starting at 0x287
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s39(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x287 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x308

    requires s0.stack[11] == 0x43

    requires s0.stack[12] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x308;
      assert s1.Peek(11) == 0x43;
      assert s1.Peek(12) == 0x48;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s40(s9, gas - 1)
  }

  /** Node 40
    * Segment Id for this node is: 58
    * Starting at 0x308
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s40(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x308 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x43

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x43;
      assert s1.Peek(7) == 0x48;
      var s2 := Swap3(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push1(s4, 0x20);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := CallDataLoad(s7);
      var s9 := Push8(s8, 0xffffffffffffffff);
      var s10 := Dup2(s9);
      var s11 := Gt(s10);
      assert s11.Peek(6) == 0x43;
      assert s11.Peek(7) == 0x48;
      var s12 := IsZero(s11);
      var s13 := Push2(s12, 0x0325);
      var s14 := JumpI(s13);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s13.stack[1] > 0 then
        ExecuteFromCFGNode_s42(s14, gas - 1)
      else
        ExecuteFromCFGNode_s41(s14, gas - 1)
  }

  /** Node 41
    * Segment Id for this node is: 59
    * Starting at 0x321
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s41(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x321 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x43

    requires s0.stack[6] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(6) == 0x43;
      assert s1.Peek(7) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 42
    * Segment Id for this node is: 60
    * Starting at 0x325
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s42(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x325 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[5] == 0x43

    requires s0.stack[6] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x43;
      assert s1.Peek(6) == 0x48;
      var s2 := Push2(s1, 0x0331);
      var s3 := Dup6(s2);
      var s4 := Dup3(s3);
      var s5 := Dup7(s4);
      var s6 := Add(s5);
      var s7 := Push2(s6, 0x0290);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s43(s8, gas - 1)
  }

  /** Node 43
    * Segment Id for this node is: 47
    * Starting at 0x290
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s43(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x290 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[2] == 0x331

    requires s0.stack[8] == 0x43

    requires s0.stack[9] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x331;
      assert s1.Peek(8) == 0x43;
      assert s1.Peek(9) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Push1(s3, 0x1f);
      var s5 := Dup4(s4);
      var s6 := Add(s5);
      var s7 := SLt(s6);
      var s8 := Push2(s7, 0x02a1);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s45(s9, gas - 1)
      else
        ExecuteFromCFGNode_s44(s9, gas - 1)
  }

  /** Node 44
    * Segment Id for this node is: 48
    * Starting at 0x29d
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s44(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x29d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x331

    requires s0.stack[9] == 0x43

    requires s0.stack[10] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(4) == 0x331;
      assert s1.Peek(10) == 0x43;
      assert s1.Peek(11) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 45
    * Segment Id for this node is: 49
    * Starting at 0x2a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 6
    * Net Stack Effect: +5
    * Net Capacity Effect: -5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s45(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 12

    requires s0.stack[3] == 0x331

    requires s0.stack[9] == 0x43

    requires s0.stack[10] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x331;
      assert s1.Peek(9) == 0x43;
      assert s1.Peek(10) == 0x48;
      var s2 := Dup2(s1);
      var s3 := CallDataLoad(s2);
      var s4 := Push2(s3, 0x02b1);
      var s5 := Dup5(s4);
      var s6 := Dup3(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup7(s7);
      var s9 := Add(s8);
      var s10 := Push2(s9, 0x01e5);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s46(s11, gas - 1)
  }

  /** Node 46
    * Segment Id for this node is: 32
    * Starting at 0x1e5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s46(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1e5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 17

    requires s0.stack[3] == 0x2b1

    requires s0.stack[8] == 0x331

    requires s0.stack[14] == 0x43

    requires s0.stack[15] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x2b1;
      assert s1.Peek(8) == 0x331;
      assert s1.Peek(14) == 0x43;
      assert s1.Peek(15) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x01f8);
      var s4 := Push2(s3, 0x01f3);
      var s5 := Dup5(s4);
      var s6 := Push2(s5, 0x041e);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s47(s7, gas - 1)
  }

  /** Node 47
    * Segment Id for this node is: 74
    * Starting at 0x41e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s47(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x41e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[1] == 0x1f3

    requires s0.stack[2] == 0x1f8

    requires s0.stack[7] == 0x2b1

    requires s0.stack[12] == 0x331

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f3;
      assert s1.Peek(2) == 0x1f8;
      assert s1.Peek(7) == 0x2b1;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push8(s2, 0xffffffffffffffff);
      var s4 := Dup3(s3);
      var s5 := Gt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0439);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s50(s8, gas - 1)
      else
        ExecuteFromCFGNode_s48(s8, gas - 1)
  }

  /** Node 48
    * Segment Id for this node is: 75
    * Starting at 0x431
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s48(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x431 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1f3

    requires s0.stack[3] == 0x1f8

    requires s0.stack[8] == 0x2b1

    requires s0.stack[13] == 0x331

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x0438);
      assert s1.Peek(0) == 0x438;
      assert s1.Peek(3) == 0x1f3;
      assert s1.Peek(4) == 0x1f8;
      assert s1.Peek(9) == 0x2b1;
      assert s1.Peek(14) == 0x331;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
      var s2 := Push2(s1, 0x050f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s49(s3, gas - 1)
  }

  /** Node 49
    * Segment Id for this node is: 89
    * Starting at 0x50f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s49(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x438

    requires s0.stack[3] == 0x1f3

    requires s0.stack[4] == 0x1f8

    requires s0.stack[9] == 0x2b1

    requires s0.stack[14] == 0x331

    requires s0.stack[20] == 0x43

    requires s0.stack[21] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x438;
      assert s1.Peek(3) == 0x1f3;
      assert s1.Peek(4) == 0x1f8;
      assert s1.Peek(9) == 0x2b1;
      assert s1.Peek(14) == 0x331;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
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

  /** Node 50
    * Segment Id for this node is: 77
    * Starting at 0x439
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s50(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x439 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[2] == 0x1f3

    requires s0.stack[3] == 0x1f8

    requires s0.stack[8] == 0x2b1

    requires s0.stack[13] == 0x331

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x1f3;
      assert s1.Peek(3) == 0x1f8;
      assert s1.Peek(8) == 0x2b1;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(19) == 0x43;
      assert s1.Peek(20) == 0x48;
      var s2 := Push1(s1, 0x20);
      var s3 := Dup3(s2);
      var s4 := Mul(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push1(s6, 0x20);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Swap1(s9);
      var s11 := Pop(s10);
      assert s11.Peek(2) == 0x1f3;
      assert s11.Peek(3) == 0x1f8;
      assert s11.Peek(8) == 0x2b1;
      assert s11.Peek(13) == 0x331;
      assert s11.Peek(19) == 0x43;
      assert s11.Peek(20) == 0x48;
      var s12 := Swap2(s11);
      var s13 := Swap1(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s51(s15, gas - 1)
  }

  /** Node 51
    * Segment Id for this node is: 33
    * Starting at 0x1f3
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s51(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1f8

    requires s0.stack[6] == 0x2b1

    requires s0.stack[11] == 0x331

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f8;
      assert s1.Peek(6) == 0x2b1;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(17) == 0x43;
      assert s1.Peek(18) == 0x48;
      var s2 := Push2(s1, 0x03c1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s52(s3, gas - 1)
  }

  /** Node 52
    * Segment Id for this node is: 66
    * Starting at 0x3c1
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s52(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3c1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[1] == 0x1f8

    requires s0.stack[6] == 0x2b1

    requires s0.stack[11] == 0x331

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x1f8;
      assert s1.Peek(6) == 0x2b1;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(17) == 0x43;
      assert s1.Peek(18) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x40);
      var s4 := MLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Dup2(s6);
      var s8 := Dup2(s7);
      var s9 := Add(s8);
      var s10 := Dup2(s9);
      var s11 := Dup2(s10);
      assert s11.Peek(5) == 0x1f8;
      assert s11.Peek(10) == 0x2b1;
      assert s11.Peek(15) == 0x331;
      assert s11.Peek(21) == 0x43;
      assert s11.Peek(22) == 0x48;
      var s12 := Lt(s11);
      var s13 := Push8(s12, 0xffffffffffffffff);
      var s14 := Dup3(s13);
      var s15 := Gt(s14);
      var s16 := Or(s15);
      var s17 := IsZero(s16);
      var s18 := Push2(s17, 0x03e8);
      var s19 := JumpI(s18);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s18.stack[1] > 0 then
        ExecuteFromCFGNode_s55(s19, gas - 1)
      else
        ExecuteFromCFGNode_s53(s19, gas - 1)
  }

  /** Node 53
    * Segment Id for this node is: 67
    * Starting at 0x3e0
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s53(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1f8

    requires s0.stack[8] == 0x2b1

    requires s0.stack[13] == 0x331

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x03e7);
      assert s1.Peek(0) == 0x3e7;
      assert s1.Peek(4) == 0x1f8;
      assert s1.Peek(9) == 0x2b1;
      assert s1.Peek(14) == 0x331;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
      var s2 := Push2(s1, 0x050f);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s54(s3, gas - 1)
  }

  /** Node 54
    * Segment Id for this node is: 89
    * Starting at 0x50f
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s54(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x50f as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[0] == 0x3e7

    requires s0.stack[4] == 0x1f8

    requires s0.stack[9] == 0x2b1

    requires s0.stack[14] == 0x331

    requires s0.stack[20] == 0x43

    requires s0.stack[21] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x3e7;
      assert s1.Peek(4) == 0x1f8;
      assert s1.Peek(9) == 0x2b1;
      assert s1.Peek(14) == 0x331;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
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

  /** Node 55
    * Segment Id for this node is: 69
    * Starting at 0x3e8
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s55(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3e8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 22

    requires s0.stack[3] == 0x1f8

    requires s0.stack[8] == 0x2b1

    requires s0.stack[13] == 0x331

    requires s0.stack[19] == 0x43

    requires s0.stack[20] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x1f8;
      assert s1.Peek(8) == 0x2b1;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(19) == 0x43;
      assert s1.Peek(20) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Push1(s2, 0x40);
      var s4 := MStore(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s56(s9, gas - 1)
  }

  /** Node 56
    * Segment Id for this node is: 34
    * Starting at 0x1f8
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s56(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x1f8 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 19

    requires s0.stack[5] == 0x2b1

    requires s0.stack[10] == 0x331

    requires s0.stack[16] == 0x43

    requires s0.stack[17] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x2b1;
      assert s1.Peek(10) == 0x331;
      assert s1.Peek(16) == 0x43;
      assert s1.Peek(17) == 0x48;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Dup1(s3);
      var s5 := Dup4(s4);
      var s6 := Dup3(s5);
      var s7 := MStore(s6);
      var s8 := Push1(s7, 0x20);
      var s9 := Dup3(s8);
      var s10 := Add(s9);
      var s11 := Swap1(s10);
      assert s11.Peek(6) == 0x2b1;
      assert s11.Peek(11) == 0x331;
      assert s11.Peek(17) == 0x43;
      assert s11.Peek(18) == 0x48;
      var s12 := Pop(s11);
      var s13 := Dup3(s12);
      var s14 := Dup6(s13);
      var s15 := Push1(s14, 0x20);
      var s16 := Dup7(s15);
      var s17 := Mul(s16);
      var s18 := Dup3(s17);
      var s19 := Add(s18);
      var s20 := Gt(s19);
      var s21 := IsZero(s20);
      assert s21.Peek(7) == 0x2b1;
      assert s21.Peek(12) == 0x331;
      assert s21.Peek(18) == 0x43;
      assert s21.Peek(19) == 0x48;
      var s22 := Push2(s21, 0x0217);
      var s23 := JumpI(s22);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s22.stack[1] > 0 then
        ExecuteFromCFGNode_s58(s23, gas - 1)
      else
        ExecuteFromCFGNode_s57(s23, gas - 1)
  }

  /** Node 57
    * Segment Id for this node is: 35
    * Starting at 0x213
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s57(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x213 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x2b1

    requires s0.stack[11] == 0x331

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(7) == 0x2b1;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 58
    * Segment Id for this node is: 36
    * Starting at 0x217
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s58(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x217 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 20

    requires s0.stack[6] == 0x2b1

    requires s0.stack[11] == 0x331

    requires s0.stack[17] == 0x43

    requires s0.stack[18] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x2b1;
      assert s1.Peek(11) == 0x331;
      assert s1.Peek(17) == 0x43;
      assert s1.Peek(18) == 0x48;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s59(s2, gas - 1)
  }

  /** Node 59
    * Segment Id for this node is: 37
    * Starting at 0x21a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s59(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x21a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x2b1

    requires s0.stack[12] == 0x331

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2b1;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Dup6(s1);
      var s3 := Dup2(s2);
      var s4 := Lt(s3);
      var s5 := IsZero(s4);
      var s6 := Push2(s5, 0x0247);
      var s7 := JumpI(s6);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s6.stack[1] > 0 then
        ExecuteFromCFGNode_s69(s7, gas - 1)
      else
        ExecuteFromCFGNode_s60(s7, gas - 1)
  }

  /** Node 60
    * Segment Id for this node is: 38
    * Starting at 0x223
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s60(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x223 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x2b1

    requires s0.stack[12] == 0x331

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup2(s0);
      assert s1.Peek(8) == 0x2b1;
      assert s1.Peek(13) == 0x331;
      assert s1.Peek(19) == 0x43;
      assert s1.Peek(20) == 0x48;
      var s2 := Push2(s1, 0x022d);
      var s3 := Dup9(s2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x02ba);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s61(s6, gas - 1)
  }

  /** Node 61
    * Segment Id for this node is: 51
    * Starting at 0x2ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s61(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 25

    requires s0.stack[2] == 0x22d

    requires s0.stack[11] == 0x2b1

    requires s0.stack[16] == 0x331

    requires s0.stack[22] == 0x43

    requires s0.stack[23] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x22d;
      assert s1.Peek(11) == 0x2b1;
      assert s1.Peek(16) == 0x331;
      assert s1.Peek(22) == 0x43;
      assert s1.Peek(23) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := CallDataLoad(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Push2(s6, 0x02c9);
      var s8 := Dup2(s7);
      var s9 := Push2(s8, 0x0555);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s62(s10, gas - 1)
  }

  /** Node 62
    * Segment Id for this node is: 94
    * Starting at 0x555
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s62(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x555 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x2c9

    requires s0.stack[5] == 0x22d

    requires s0.stack[14] == 0x2b1

    requires s0.stack[19] == 0x331

    requires s0.stack[25] == 0x43

    requires s0.stack[26] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2c9;
      assert s1.Peek(5) == 0x22d;
      assert s1.Peek(14) == 0x2b1;
      assert s1.Peek(19) == 0x331;
      assert s1.Peek(25) == 0x43;
      assert s1.Peek(26) == 0x48;
      var s2 := Push2(s1, 0x055e);
      var s3 := Dup2(s2);
      var s4 := Push2(s3, 0x048d);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s63(s5, gas - 1)
  }

  /** Node 63
    * Segment Id for this node is: 82
    * Starting at 0x48d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s63(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 30

    requires s0.stack[1] == 0x55e

    requires s0.stack[3] == 0x2c9

    requires s0.stack[7] == 0x22d

    requires s0.stack[16] == 0x2b1

    requires s0.stack[21] == 0x331

    requires s0.stack[27] == 0x43

    requires s0.stack[28] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x55e;
      assert s1.Peek(3) == 0x2c9;
      assert s1.Peek(7) == 0x22d;
      assert s1.Peek(16) == 0x2b1;
      assert s1.Peek(21) == 0x331;
      assert s1.Peek(27) == 0x43;
      assert s1.Peek(28) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s64(s9, gas - 1)
  }

  /** Node 64
    * Segment Id for this node is: 95
    * Starting at 0x55e
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s64(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x55e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 29

    requires s0.stack[2] == 0x2c9

    requires s0.stack[6] == 0x22d

    requires s0.stack[15] == 0x2b1

    requires s0.stack[20] == 0x331

    requires s0.stack[26] == 0x43

    requires s0.stack[27] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x2c9;
      assert s1.Peek(6) == 0x22d;
      assert s1.Peek(15) == 0x2b1;
      assert s1.Peek(20) == 0x331;
      assert s1.Peek(26) == 0x43;
      assert s1.Peek(27) == 0x48;
      var s2 := Dup2(s1);
      var s3 := Eq(s2);
      var s4 := Push2(s3, 0x0569);
      var s5 := JumpI(s4);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s4.stack[1] > 0 then
        ExecuteFromCFGNode_s66(s5, gas - 1)
      else
        ExecuteFromCFGNode_s65(s5, gas - 1)
  }

  /** Node 65
    * Segment Id for this node is: 96
    * Starting at 0x565
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s65(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x565 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x2c9

    requires s0.stack[5] == 0x22d

    requires s0.stack[14] == 0x2b1

    requires s0.stack[19] == 0x331

    requires s0.stack[25] == 0x43

    requires s0.stack[26] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x00);
      assert s1.Peek(2) == 0x2c9;
      assert s1.Peek(6) == 0x22d;
      assert s1.Peek(15) == 0x2b1;
      assert s1.Peek(20) == 0x331;
      assert s1.Peek(26) == 0x43;
      assert s1.Peek(27) == 0x48;
      var s2 := Dup1(s1);
      var s3 := Revert(s2);
      // Segment is terminal (Revert, Stop or Return)
      s3
  }

  /** Node 66
    * Segment Id for this node is: 97
    * Starting at 0x569
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s66(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x569 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 28

    requires s0.stack[1] == 0x2c9

    requires s0.stack[5] == 0x22d

    requires s0.stack[14] == 0x2b1

    requires s0.stack[19] == 0x331

    requires s0.stack[25] == 0x43

    requires s0.stack[26] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x2c9;
      assert s1.Peek(5) == 0x22d;
      assert s1.Peek(14) == 0x2b1;
      assert s1.Peek(19) == 0x331;
      assert s1.Peek(25) == 0x43;
      assert s1.Peek(26) == 0x48;
      var s2 := Pop(s1);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s67(s3, gas - 1)
  }

  /** Node 67
    * Segment Id for this node is: 52
    * Starting at 0x2c9
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s67(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2c9 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 26

    requires s0.stack[3] == 0x22d

    requires s0.stack[12] == 0x2b1

    requires s0.stack[17] == 0x331

    requires s0.stack[23] == 0x43

    requires s0.stack[24] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x22d;
      assert s1.Peek(12) == 0x2b1;
      assert s1.Peek(17) == 0x331;
      assert s1.Peek(23) == 0x43;
      assert s1.Peek(24) == 0x48;
      var s2 := Swap3(s1);
      var s3 := Swap2(s2);
      var s4 := Pop(s3);
      var s5 := Pop(s4);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s68(s6, gas - 1)
  }

  /** Node 68
    * Segment Id for this node is: 39
    * Starting at 0x22d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 5
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s68(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 23

    requires s0.stack[9] == 0x2b1

    requires s0.stack[14] == 0x331

    requires s0.stack[20] == 0x43

    requires s0.stack[21] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(9) == 0x2b1;
      assert s1.Peek(14) == 0x331;
      assert s1.Peek(20) == 0x43;
      assert s1.Peek(21) == 0x48;
      var s2 := Dup5(s1);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Dup5(s4);
      var s6 := Add(s5);
      var s7 := Swap4(s6);
      var s8 := Pop(s7);
      var s9 := Push1(s8, 0x20);
      var s10 := Dup4(s9);
      var s11 := Add(s10);
      assert s11.Peek(9) == 0x2b1;
      assert s11.Peek(14) == 0x331;
      assert s11.Peek(20) == 0x43;
      assert s11.Peek(21) == 0x48;
      var s12 := Swap3(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Push1(s14, 0x01);
      var s16 := Dup2(s15);
      var s17 := Add(s16);
      var s18 := Swap1(s17);
      var s19 := Pop(s18);
      var s20 := Push2(s19, 0x021a);
      var s21 := Jump(s20);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s59(s21, gas - 1)
  }

  /** Node 69
    * Segment Id for this node is: 40
    * Starting at 0x247
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 8
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -7
    * Net Capacity Effect: +7
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s69(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x247 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 21

    requires s0.stack[7] == 0x2b1

    requires s0.stack[12] == 0x331

    requires s0.stack[18] == 0x43

    requires s0.stack[19] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x2b1;
      assert s1.Peek(12) == 0x331;
      assert s1.Peek(18) == 0x43;
      assert s1.Peek(19) == 0x48;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap4(s4);
      var s6 := Swap3(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s70(s10, gas - 1)
  }

  /** Node 70
    * Segment Id for this node is: 50
    * Starting at 0x2b1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 6
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s70(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x2b1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 14

    requires s0.stack[5] == 0x331

    requires s0.stack[11] == 0x43

    requires s0.stack[12] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x331;
      assert s1.Peek(11) == 0x43;
      assert s1.Peek(12) == 0x48;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Swap3(s4);
      var s6 := Swap2(s5);
      var s7 := Pop(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s71(s9, gas - 1)
  }

  /** Node 71
    * Segment Id for this node is: 61
    * Starting at 0x331
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 7
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -5
    * Net Capacity Effect: +5
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s71(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x331 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[6] == 0x43

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(6) == 0x43;
      assert s1.Peek(7) == 0x48;
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
      ExecuteFromCFGNode_s72(s10, gas - 1)
  }

  /** Node 72
    * Segment Id for this node is: 7
    * Starting at 0x43
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s72(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x43 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x48;
      var s2 := Push2(s1, 0x004a);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s73(s3, gas - 1)
  }

  /** Node 73
    * Segment Id for this node is: 9
    * Starting at 0x4a
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s73(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x48;
      var s2 := Dup1(s1);
      var s3 := MLoad(s2);
      var s4 := Dup3(s3);
      var s5 := MLoad(s4);
      var s6 := Eq(s5);
      var s7 := Push2(s6, 0x008e);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s81(s8, gas - 1)
      else
        ExecuteFromCFGNode_s74(s8, gas - 1)
  }

  /** Node 74
    * Segment Id for this node is: 10
    * Starting at 0x54
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s74(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x54 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push1(s0, 0x40);
      assert s1.Peek(3) == 0x48;
      var s2 := MLoad(s1);
      var s3 := Push32(s2, 0x08c379a000000000000000000000000000000000000000000000000000000000);
      var s4 := Dup2(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x04);
      var s7 := Add(s6);
      var s8 := Push2(s7, 0x0085);
      var s9 := Swap1(s8);
      var s10 := Push2(s9, 0x03a1);
      var s11 := Jump(s10);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s75(s11, gas - 1)
  }

  /** Node 75
    * Segment Id for this node is: 64
    * Starting at 0x3a1
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s75(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3a1 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[1] == 0x85

    requires s0.stack[4] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x85;
      assert s1.Peek(4) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push1(s2, 0x20);
      var s4 := Dup3(s3);
      var s5 := Add(s4);
      var s6 := Swap1(s5);
      var s7 := Pop(s6);
      var s8 := Dup2(s7);
      var s9 := Dup2(s8);
      var s10 := Sub(s9);
      var s11 := Push1(s10, 0x00);
      assert s11.Peek(4) == 0x85;
      assert s11.Peek(7) == 0x48;
      var s12 := Dup4(s11);
      var s13 := Add(s12);
      var s14 := MStore(s13);
      var s15 := Push2(s14, 0x03ba);
      var s16 := Dup2(s15);
      var s17 := Push2(s16, 0x033b);
      var s18 := Jump(s17);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s76(s18, gas - 1)
  }

  /** Node 76
    * Segment Id for this node is: 62
    * Starting at 0x33b
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 5
    * Net Stack Effect: +4
    * Net Capacity Effect: -4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s76(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x33b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[1] == 0x3ba

    requires s0.stack[4] == 0x85

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x3ba;
      assert s1.Peek(4) == 0x85;
      assert s1.Peek(7) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x0348);
      var s4 := Push1(s3, 0x38);
      var s5 := Dup4(s4);
      var s6 := Push2(s5, 0x044a);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s77(s7, gas - 1)
  }

  /** Node 77
    * Segment Id for this node is: 78
    * Starting at 0x44a
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s77(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x44a as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 13

    requires s0.stack[2] == 0x348

    requires s0.stack[5] == 0x3ba

    requires s0.stack[8] == 0x85

    requires s0.stack[11] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x348;
      assert s1.Peek(5) == 0x3ba;
      assert s1.Peek(8) == 0x85;
      assert s1.Peek(11) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup3(s2);
      var s4 := Dup3(s3);
      var s5 := MStore(s4);
      var s6 := Push1(s5, 0x20);
      var s7 := Dup3(s6);
      var s8 := Add(s7);
      var s9 := Swap1(s8);
      var s10 := Pop(s9);
      var s11 := Swap3(s10);
      assert s11.Peek(0) == 0x348;
      assert s11.Peek(6) == 0x3ba;
      assert s11.Peek(9) == 0x85;
      assert s11.Peek(12) == 0x48;
      var s12 := Swap2(s11);
      var s13 := Pop(s12);
      var s14 := Pop(s13);
      var s15 := Jump(s14);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s78(s15, gas - 1)
  }

  /** Node 78
    * Segment Id for this node is: 63
    * Starting at 0x348
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s78(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x348 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[3] == 0x3ba

    requires s0.stack[6] == 0x85

    requires s0.stack[9] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x3ba;
      assert s1.Peek(6) == 0x85;
      assert s1.Peek(9) == 0x48;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0x526563697069656e747320616e6420616d6f756e747320617272617973206d75);
      var s5 := Push1(s4, 0x00);
      var s6 := Dup4(s5);
      var s7 := Add(s6);
      var s8 := MStore(s7);
      var s9 := Push32(s8, 0x7374206265206f66207468652073616d65206c656e6774680000000000000000);
      var s10 := Push1(s9, 0x20);
      var s11 := Dup4(s10);
      assert s11.Peek(5) == 0x3ba;
      assert s11.Peek(8) == 0x85;
      assert s11.Peek(11) == 0x48;
      var s12 := Add(s11);
      var s13 := MStore(s12);
      var s14 := Push1(s13, 0x40);
      var s15 := Dup3(s14);
      var s16 := Add(s15);
      var s17 := Swap1(s16);
      var s18 := Pop(s17);
      var s19 := Swap2(s18);
      var s20 := Swap1(s19);
      var s21 := Pop(s20);
      assert s21.Peek(0) == 0x3ba;
      assert s21.Peek(4) == 0x85;
      assert s21.Peek(7) == 0x48;
      var s22 := Jump(s21);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s79(s22, gas - 1)
  }

  /** Node 79
    * Segment Id for this node is: 65
    * Starting at 0x3ba
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s79(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x3ba as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[3] == 0x85

    requires s0.stack[6] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x85;
      assert s1.Peek(6) == 0x48;
      var s2 := Swap1(s1);
      var s3 := Pop(s2);
      var s4 := Swap2(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Jump(s6);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s80(s7, gas - 1)
  }

  /** Node 80
    * Segment Id for this node is: 11
    * Starting at 0x85
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s80(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x85 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x48;
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

  /** Node 81
    * Segment Id for this node is: 12
    * Starting at 0x8e
    * Segment type is: CONT Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s81(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x8e as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 4

    requires s0.stack[2] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x48;
      var s2 := Push1(s1, 0x00);
      //  Go to the next instruction at pc + 1
      ExecuteFromCFGNode_s82(s2, gas - 1)
  }

  /** Node 82
    * Segment Id for this node is: 13
    * Starting at 0x91
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s82(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x91 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x48;
      var s2 := Dup3(s1);
      var s3 := MLoad(s2);
      var s4 := Dup2(s3);
      var s5 := Lt(s4);
      var s6 := IsZero(s5);
      var s7 := Push2(s6, 0x0174);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s97(s8, gas - 1)
      else
        ExecuteFromCFGNode_s83(s8, gas - 1)
  }

  /** Node 83
    * Segment Id for this node is: 14
    * Starting at 0x9b
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s83(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x9b as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Dup3(s0);
      assert s1.Peek(4) == 0x48;
      var s2 := Dup2(s1);
      var s3 := Dup2(s2);
      var s4 := MLoad(s3);
      var s5 := Dup2(s4);
      var s6 := Lt(s5);
      var s7 := Push2(s6, 0x00d3);
      var s8 := JumpI(s7);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s7.stack[1] > 0 then
        ExecuteFromCFGNode_s85(s8, gas - 1)
      else
        ExecuteFromCFGNode_s84(s8, gas - 1)
  }

  /** Node 84
    * Segment Id for this node is: 15
    * Starting at 0xa5
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s84(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xa5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      assert s1.Peek(6) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x32);
      var s5 := Push1(s4, 0x04);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Push1(s7, 0x00);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 85
    * Segment Id for this node is: 16
    * Starting at 0xd3
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s85(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xd3 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x48;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Push20(s7, 0xffffffffffffffffffffffffffffffffffffffff);
      var s9 := And(s8);
      var s10 := Push2(s9, 0x08fc);
      var s11 := Dup4(s10);
      assert s11.Peek(6) == 0x48;
      var s12 := Dup4(s11);
      var s13 := Dup2(s12);
      var s14 := MLoad(s13);
      var s15 := Dup2(s14);
      var s16 := Lt(s15);
      var s17 := Push2(s16, 0x012d);
      var s18 := JumpI(s17);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s17.stack[1] > 0 then
        ExecuteFromCFGNode_s87(s18, gas - 1)
      else
        ExecuteFromCFGNode_s86(s18, gas - 1)
  }

  /** Node 86
    * Segment Id for this node is: 17
    * Starting at 0xff
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s86(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0xff as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push32(s0, 0x4e487b7100000000000000000000000000000000000000000000000000000000);
      assert s1.Peek(8) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := MStore(s2);
      var s4 := Push1(s3, 0x32);
      var s5 := Push1(s4, 0x04);
      var s6 := MStore(s5);
      var s7 := Push1(s6, 0x24);
      var s8 := Push1(s7, 0x00);
      var s9 := Revert(s8);
      // Segment is terminal (Revert, Stop or Return)
      s9
  }

  /** Node 87
    * Segment Id for this node is: 18
    * Starting at 0x12d
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 8
    * Net Stack Effect: -3
    * Net Capacity Effect: +3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s87(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x12d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(7) == 0x48;
      var s2 := Push1(s1, 0x20);
      var s3 := Mul(s2);
      var s4 := Push1(s3, 0x20);
      var s5 := Add(s4);
      var s6 := Add(s5);
      var s7 := MLoad(s6);
      var s8 := Swap1(s7);
      var s9 := Dup2(s8);
      var s10 := IsZero(s9);
      var s11 := Mul(s10);
      assert s11.Peek(6) == 0x48;
      var s12 := Swap1(s11);
      var s13 := Push1(s12, 0x40);
      var s14 := MLoad(s13);
      var s15 := Push1(s14, 0x00);
      var s16 := Push1(s15, 0x40);
      var s17 := MLoad(s16);
      var s18 := Dup1(s17);
      var s19 := Dup4(s18);
      var s20 := Sub(s19);
      var s21 := Dup2(s20);
      assert s21.Peek(11) == 0x48;
      var s22 := Dup6(s21);
      var s23 := Dup9(s22);
      var s24 := Dup9(s23);
      var s25 := Call(s24);
      var s26 := Swap4(s25);
      var s27 := Pop(s26);
      var s28 := Pop(s27);
      var s29 := Pop(s28);
      var s30 := Pop(s29);
      var s31 := IsZero(s30);
      assert s31.Peek(4) == 0x48;
      var s32 := Dup1(s31);
      var s33 := IsZero(s32);
      var s34 := Push2(s33, 0x0160);
      var s35 := JumpI(s34);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s34.stack[1] > 0 then
        ExecuteFromCFGNode_s89(s35, gas - 1)
      else
        ExecuteFromCFGNode_s88(s35, gas - 1)
  }

  /** Node 88
    * Segment Id for this node is: 19
    * Starting at 0x157
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s88(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x157 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := ReturnDataSize(s0);
      assert s1.Peek(5) == 0x48;
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
    * Segment Id for this node is: 20
    * Starting at 0x160
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 3
    * Net Stack Effect: +2
    * Net Capacity Effect: -2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s89(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x160 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 6

    requires s0.stack[4] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(4) == 0x48;
      var s2 := Pop(s1);
      var s3 := Dup1(s2);
      var s4 := Dup1(s3);
      var s5 := Push2(s4, 0x016c);
      var s6 := Swap1(s5);
      var s7 := Push2(s6, 0x0497);
      var s8 := Jump(s7);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s90(s8, gas - 1)
  }

  /** Node 90
    * Segment Id for this node is: 83
    * Starting at 0x497
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 1
    * Minimum capacity for this segment to prevent stack overflow: 4
    * Net Stack Effect: +3
    * Net Capacity Effect: -3
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s90(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x497 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 8

    requires s0.stack[1] == 0x16c

    requires s0.stack[6] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x16c;
      assert s1.Peek(6) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Push2(s2, 0x04a2);
      var s4 := Dup3(s3);
      var s5 := Push2(s4, 0x048d);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s91(s6, gas - 1)
  }

  /** Node 91
    * Segment Id for this node is: 82
    * Starting at 0x48d
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 2
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s91(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48d as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 11

    requires s0.stack[1] == 0x4a2

    requires s0.stack[4] == 0x16c

    requires s0.stack[9] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(1) == 0x4a2;
      assert s1.Peek(4) == 0x16c;
      assert s1.Peek(9) == 0x48;
      var s2 := Push1(s1, 0x00);
      var s3 := Dup2(s2);
      var s4 := Swap1(s3);
      var s5 := Pop(s4);
      var s6 := Swap2(s5);
      var s7 := Swap1(s6);
      var s8 := Pop(s7);
      var s9 := Jump(s8);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s92(s9, gas - 1)
  }

  /** Node 92
    * Segment Id for this node is: 84
    * Starting at 0x4a2
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 1
    * Net Stack Effect: -1
    * Net Capacity Effect: +1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s92(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4a2 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[3] == 0x16c

    requires s0.stack[8] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x16c;
      assert s1.Peek(8) == 0x48;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Push32(s3, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      var s5 := Dup3(s4);
      var s6 := Eq(s5);
      var s7 := IsZero(s6);
      var s8 := Push2(s7, 0x04d5);
      var s9 := JumpI(s8);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s8.stack[1] > 0 then
        ExecuteFromCFGNode_s95(s9, gas - 1)
      else
        ExecuteFromCFGNode_s93(s9, gas - 1)
  }

  /** Node 93
    * Segment Id for this node is: 85
    * Starting at 0x4cd
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +1
    * Net Capacity Effect: -1
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s93(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4cd as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x16c

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Push2(s0, 0x04d4);
      assert s1.Peek(0) == 0x4d4;
      assert s1.Peek(3) == 0x16c;
      assert s1.Peek(8) == 0x48;
      var s2 := Push2(s1, 0x04e0);
      var s3 := Jump(s2);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s94(s3, gas - 1)
  }

  /** Node 94
    * Segment Id for this node is: 88
    * Starting at 0x4e0
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s94(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4e0 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 10

    requires s0.stack[0] == 0x4d4

    requires s0.stack[3] == 0x16c

    requires s0.stack[8] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(0) == 0x4d4;
      assert s1.Peek(3) == 0x16c;
      assert s1.Peek(8) == 0x48;
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

  /** Node 95
    * Segment Id for this node is: 87
    * Starting at 0x4d5
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s95(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x4d5 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 9

    requires s0.stack[2] == 0x16c

    requires s0.stack[7] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(2) == 0x16c;
      assert s1.Peek(7) == 0x48;
      var s2 := Push1(s1, 0x01);
      var s3 := Dup3(s2);
      var s4 := Add(s3);
      var s5 := Swap1(s4);
      var s6 := Pop(s5);
      var s7 := Swap2(s6);
      var s8 := Swap1(s7);
      var s9 := Pop(s8);
      var s10 := Jump(s9);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s96(s10, gas - 1)
  }

  /** Node 96
    * Segment Id for this node is: 21
    * Starting at 0x16c
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 3
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -2
    * Net Capacity Effect: +2
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s96(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x16c as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 7

    requires s0.stack[5] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(5) == 0x48;
      var s2 := Swap2(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Push2(s4, 0x0091);
      var s6 := Jump(s5);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s82(s6, gas - 1)
  }

  /** Node 97
    * Segment Id for this node is: 22
    * Starting at 0x174
    * Segment type is: JUMP Segment
    * Minimum stack size for this segment to prevent stack underflow: 4
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: -4
    * Net Capacity Effect: +4
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s97(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x174 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 5

    requires s0.stack[3] == 0x48

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      assert s1.Peek(3) == 0x48;
      var s2 := Pop(s1);
      var s3 := Pop(s2);
      var s4 := Pop(s3);
      var s5 := Jump(s4);
      //  JUMP to the target at Peek(0)
      ExecuteFromCFGNode_s98(s5, gas - 1)
  }

  /** Node 98
    * Segment Id for this node is: 8
    * Starting at 0x48
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s98(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x48 as nat
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

  /** Node 99
    * Segment Id for this node is: 3
    * Starting at 0x22
    * Segment type is: JUMPI Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s99(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x22 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := JumpDest(s0);
      var s2 := CallDataSize(s1);
      var s3 := Push2(s2, 0x0029);
      var s4 := JumpI(s3);
      // This is a JUMPI segment, determine next pc using second top-most element of stack
      if s3.stack[1] > 0 then
        ExecuteFromCFGNode_s101(s4, gas - 1)
      else
        ExecuteFromCFGNode_s100(s4, gas - 1)
  }

  /** Node 100
    * Segment Id for this node is: 4
    * Starting at 0x28
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 0
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s100(s0: EState, gas: nat): (s': EState)
    // PC requirement for this node.
    requires s0.pc == 0x28 as nat
    // Stack requirements for this node.
    requires s0.Operands() >= 0

    decreases gas
  {
    if gas == 0 then s0
    else
      var s1 := Stop(s0);
      // Segment is terminal (Revert, Stop or Return)
      s1
  }

  /** Node 101
    * Segment Id for this node is: 5
    * Starting at 0x29
    * Segment type is: STOP Segment
    * Minimum stack size for this segment to prevent stack underflow: 0
    * Minimum capacity for this segment to prevent stack overflow: 2
    * Net Stack Effect: +0
    * Net Capacity Effect: +0
    */
  function {:opaque} {:verify true} ExecuteFromCFGNode_s101(s0: EState, gas: nat): (s': EState)
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
